// server.c

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2016 Joris van der Geer.
 */

/* server side of local client-server interface

  A remote client, typically only one, conects to a set of local clients via a proxy.
  A local client connects to a set of local servers.

  A local tripover server receives and answers journey queries.
  Servers may serve specific regions. Both local and remote clients get enough network data
  from the server at init that they can validate locations and direct to regions.

  The server loads and inialises the network, then loops for queries
  it may restart to get a fresh network snapshot, or update real-time changes
  multiple server instances may be running to support above reloads, and provide redundancy.
  However, these may run on different machines. the remote client need to know the location of such instances.

  The client interface posts its queries, and one server picks it up
  at timeout, client can re-post

  a separate network proxy can provide http-style interface, forwarding to a local client
 */

#include <unistd.h>
#include <string.h>
#include <stdlib.h>

#include "base.h"
#include "cfg.h"
#include "os.h"
#include "thread.h"
#include "mem.h"
#include "server.h"

static ub4 msgfile;
#include "msg.h"

#include "iadr.h"
#include "util.h"
#include "time.h"

#include "netbase.h"
#include "net.h"
#include "fare.h"

#include "search.h"

static int memeq(const char *s,const char *q,ub4 n) { return !memcmp(s,q,n); }

static ub1 hexmap[256];

static void mkhexmap(void)
{
  char c;

  memset(hexmap,0xff,256);
  for (c = '0'; c <= '9'; c++) hexmap[(ub4)c] = (ub1)(c - '0');
  for (c = 'a'; c <= 'f'; c++) hexmap[(ub4)c] = (ub1)(c + 10 - 'a');
  for (c = 'A'; c <= 'F'; c++) hexmap[(ub4)c] = (ub1)(c + 10 - 'A');
  hexmap[9] = 0x20;
  hexmap[0x0a] = 0xfe;
  hexmap[0x20] = 0x20;
}

static ub4 bitsinmask[256];

static void mkbitmask(void)
{
  ub4 x,xx,n;

  for (x = 0; x < 256; x++) {
    n = 0; xx = x;
    while (xx) { if (xx & 1) n++; xx >>= 1; }
    bitsinmask[x] = n;
  }
}

static ub1 idmap[256];

static void addid(ub4 from,ub4 to)
{
  ub4 i;

  for (i = from; i <= to; i++) idmap[i] = 1;
}

static int isid(char c)
{
  ub4 i = (ub4)c;
  if (i > 255) return 0;
  return idmap[i];
}

static void mkidmap(void)
{
  addid('A','Z');
  addid('a','z');
  addid('_','_');
  addid('.','.');
}

enum Cmds { Cmd_nil,Cmd_plan,Cmd_upd,Cmd_geo,Cmd_stop,Cmd_cnt };

static int cmd_geo(struct myfile *req)
{
  struct myfile rep;
  char *vp,*lp = req->buf;
  ub4 n,pos = 0,len = (ub4)req->len;
  ub4 ival;
  ub4 varstart,varend,varlen,valstart,valend,type;
  ub4 lat = 0,lon = 0,scale = 1;
  ub4 dep;
  ub4 txmask = 0xff;
  int rv;

  enum Vars {
    Cnone,
    Clat,
    Clon,
    Cscale,
    Ctxmask
  } var;

  if (len == 0) return 1;

  oclear(rep);

  while (pos < len && isid(lp[pos])) {
    ival = 0;
    varstart = varend = pos;
    while (varend < len && isid(lp[varend])) varend++;
    varlen = varend - varstart; pos = varend;
    if (varlen == 0) break;

    while (pos < len && lp[pos] == ' ') pos++;
    if (pos == len) break;
    type = lp[pos++];
    if (type == '\n' || pos == len) break;
    while (pos < len && lp[pos] == ' ') pos++;
    lp[varend] = 0;

    valstart = valend = pos;
    while (valend < len && lp[valend] != '\n') valend++;
    if (valend == len) break;
    pos = valend;
    while (pos < len && lp[pos] != '\n') pos++;
    if (lp[pos] == '\n') pos++;
    if (pos == len) break;
    lp[valend] = 0;

    if (type == 'i') {
      n = str2ub4(lp + valstart,&ival);
      if (n == 0) {
        warn(0,"expected integer for %s, found '%.*s'",lp + varstart,valend - valstart,lp + valstart);
        continue;
      }
    } else if (type == 'x') {
      n = hex2ub4(lp + valstart,&ival);
      if (n == 0) {
        warn(0,"expected hex integer for %s, found '%.*s'",lp + varstart,valend - valstart,lp + valstart);
        continue;
      }
    } else if (type == 'b') {
      n = bstr2ub4(lp + valstart,&ival);
      if (n == 0) {
        warn(0,"expected integer for %s, found '%.*s'",lp + varstart,valend - valstart,lp + valstart);
        continue;
      }
    } else {
      warn(0,"skip unknown type %c for %s '%.*s'",type,lp + varstart,valend - valstart,lp + valstart);
      continue;
    }
    vp = lp + varstart;
    vrb0(0,"len %u %.*s",varlen,varlen,vp);
    if (varlen == 3 && memeq(vp,"lat",3)) var = Clat;
    else if (varlen == 3 && memeq(vp,"lon",3)) var = Clon;
    else if (varlen == 5 && memeq(vp,"scale",5)) var = Cscale;
    else if (varlen == 6 && memeq(vp,"txmask",6)) var = Ctxmask;
    else {
      warn(0,"ignoring unknown var '%s'",vp);
      var = Cnone;
    }
    switch (var) {
    case Cnone: break;
    case Clat: lat = ival; break;
    case Clon: lon = ival; break;
    case Cscale: scale = ival; break;
    case Ctxmask: txmask = ival; break;
    }
  }

  if (txmask == 0) {
    warn(0,"txmask %x",txmask);
    txmask = 0xff;
  } else if (txmask > 0xff) {
    warn(0,"txmask %x",txmask);
    txmask = 0xff;
  }

  dep = geocode2(lat,lon,scale,(ub1)txmask,&rep);
  rv = (dep == hi32 ? 1 : 0);
  rv |= setqentry(req,&rep,".rep");
  return rv;
}

// parse parameters and invoke actual planning. Runs optionally in separate process
// to be elaborated: temporary simple interface
static int cmd_plan(gnet *net,struct myfile *req,search *src)
{
  struct myfile rep;
  char *vp,*lp = req->buf;
  ub4 n,pos = 0,len = (ub4)req->len;
  ub4 ival;
  ub4 varstart,varend,varlen,valstart,valend,type;

  ub4 portcnt = net->portcnt;
  ub4 sportcnt = net->sportcnt;

  ub4 dep = hi32,arr = hi32,lostop = 0,histop = 5,tdep = 0,ttdep = 0,utcofs = 2200,dsputcofs = 2600;
  ub4 deplat = 0,deplon = 0,arrlat = 0,arrlon = 0,scale = 1;
  enum srcmodes srcmode = Srchitime;
  ub4 ntop = 3;
  ub4 plushour = 12,minhour = 0;
  ub4 costperstop = 1;
  ub4 *mintts = src->mintts;
  ub4 walklimit = globs.walklimit;
  ub4 sumwalklimit = globs.sumwalklimit;
  ub4 walkspeed = globs.walkspeed;
  ub4 txmask = 0xff;
  ub4 nethistop = hi32;
  ub4 testiter = 0;
  ub4 tlimit = 2;
  ub4 repoptions = 0;
  ub4 msgtid = src->msgtid;

  int rv;
  enum Vars {
    Cnone,
    Cdep,
    Carr,
    Cscale,
    Cdeplat,
    Cdeplon,
    Carrlat,
    Carrlon,
    Ctdep,
    Cttdep,
    Cplushour,
    Cminhour,
    Clostop,
    Chistop,

    CminttAA,
    CminttAa,
    Cminttaa,
    CminttaA,
    CminttAx,
    CminttxA,
    Cminttax,
    Cminttxa,

    Cminttbx,
    Cminttxb,
    Cmintttt,
    Cminttxf,
    Cminttfx,

    Ccostperstop,
    Csrcmode,
    Cwalklimit,
    Cwalkspeed,
    Csumwalklimit,
    Cnethistop,
    Cutcofs,
    Cdsputcofs,
    Ctxmask,
    Ctlimit,
    Cntop,
    Crepoptions,
    Ctestiter
  } var;

  ub2 *evpool = src->evpool;
  ub1 *infconns = src->infconns;
  ub4 *infdaconns = src->infdaconns;
  ub4 seq = src->cmdseq;

  clear(src);

  src->evpool = evpool;
  src->infconns = infconns;
  src->infdaconns = infdaconns;
  src->cmdseq = seq;

  sassert(Elemcnt(globs.mintts) > Kindcnt * Kindcnt,"x");

  memcpy(mintts,globs.mintts,sizeof(globs.mintts));

  if (len == 0) return error0(msgtid,"empty request");

  oclear(rep);

  while (pos < len && isid(lp[pos])) {
    ival = 0;
    varstart = varend = pos;
    while (varend < len && isid(lp[varend])) varend++;
    varlen = varend - varstart; pos = varend;
    if (varlen == 0) break;

    while (pos < len && lp[pos] == ' ') pos++;
    if (pos == len) break;
    type = lp[pos++];
    if (type == '\n' || pos == len) break;
    while (pos < len && lp[pos] == ' ') pos++;
    lp[varend] = 0;

    valstart = valend = pos;
    while (valend < len && lp[valend] != '\n') valend++;
    if (valend == len) break;
    pos = valend;
    while (pos < len && lp[pos] != '\n') pos++;
    if (lp[pos] == '\n') pos++;
    if (pos == len) break;
    lp[valend] = 0;

    if (type == 'i') {
      n = str2ub4(lp + valstart,&ival);
      if (n == 0) {
        warn(msgtid,"expected integer for %s, found '%.*s'",lp + varstart,valend - valstart,lp + valstart);
        continue;
      }
    } else if (type == 'x') {
      n = hex2ub4(lp + valstart,&ival);
      if (n == 0) {
        warn(msgtid,"expected hex integer for %s, found '%.*s'",lp + varstart,valend - valstart,lp + valstart);
        continue;
      }
    } else if (type == 'b') {
      n = bstr2ub4(lp + valstart,&ival);
      if (n == 0) {
        warn(msgtid,"expected integer for %s, found '%.*s'",lp + varstart,valend - valstart,lp + valstart);
        continue;
      }
    } else {
      warn(msgtid,"skip unknown type %c for %s '%.*s'",type,lp + varstart,valend - valstart,lp + valstart);
      continue;
    }
    vp = lp + varstart;
    if (varlen == 3 && memeq(vp,"dep",3)) var = Cdep;
    else if (varlen == 3 && memeq(vp,"arr",3)) var = Carr;
    else if (varlen == 5 && memeq(vp,"scale",5)) var = Cscale;
    else if (varlen == 6 && memeq(vp,"deplat",6)) var = Cdeplat;
    else if (varlen == 6 && memeq(vp,"deplon",6)) var = Cdeplon;
    else if (varlen == 6 && memeq(vp,"arrlat",6)) var = Carrlat;
    else if (varlen == 6 && memeq(vp,"arrlon",6)) var = Carrlon;

    else if (varlen == 8 && memeq(vp,"depttmin",8)) var = Cttdep;
    else if (varlen == 8 && memeq(vp,"plushour",8)) var = Cplushour;
    else if (varlen == 6 && memeq(vp,"lostop",6)) var = Clostop;
    else if (varlen == 6 && memeq(vp,"histop",6)) var = Chistop;

    else if (varlen == 7) {
      if (memeq(vp,"minttAA",7)) var = CminttAA;
      else if (memeq(vp,"minttAa",7)) var = CminttAa;
      else if (memeq(vp,"minttaa",7)) var = Cminttaa;
      else if (memeq(vp,"minttaA",7)) var = CminttaA;
      else if (memeq(vp,"minttAx",7)) var = CminttAx;
      else if (memeq(vp,"minttxA",7)) var = CminttxA;
      else if (memeq(vp,"minttax",7)) var = Cminttax;
      else if (memeq(vp,"minttxa",7)) var = Cminttxa;

      else if (memeq(vp,"minttbx",7)) var = Cminttbx;
      else if (memeq(vp,"minttxb",7)) var = Cminttxb;
      else if (memeq(vp,"mintttt",7)) var = Cmintttt;
      else if (memeq(vp,"minttxf",7)) var = Cminttxf;
      else if (memeq(vp,"minttfx",7)) var = Cminttfx;

      else if (memeq(vp,"srcmode",7)) var = Csrcmode;
      else if (memeq(vp,"deptmin",7)) var = Ctdep;
      else if (memeq(vp,"minhour",7)) var = Cminhour;
      else { warn(0,"ignoring unknown var '%s'",vp); var = Cnone; }
    }
    else if (varlen == 11 && memeq(vp,"costperstop",11)) var = Ccostperstop;

    else if (varlen == 9 && memeq(vp,"walklimit",9)) var = Cwalklimit;
    else if (varlen == 9 && memeq(vp,"walkspeed",9)) var = Cwalkspeed;
    else if (varlen == 12 && memeq(vp,"sumwalklimit",12)) var = Csumwalklimit;

    else if (varlen == 9 && memeq(vp,"nethistop",9)) var = Cnethistop;
    else if (varlen == 6 && memeq(vp,"utcofs",6)) var = Cutcofs;
    else if (varlen == 9 && memeq(vp,"dsputcofs",9)) var = Cdsputcofs;
    else if (varlen == 6 && memeq(vp,"txmask",6)) var = Ctxmask;
    else if (varlen == 6 && memeq(vp,"tlimit",6)) var = Ctlimit;
    else if (varlen == 4 && memeq(vp,"ntop",4)) var = Cntop;
    else if (varlen == 10 && memeq(vp,"repoptions",10)) var = Crepoptions;
    else if (varlen == 8 && memeq(vp,"testiter",8)) var = Ctestiter;
    else {
      warn(msgtid,"ignoring unknown var '%s'",vp);
      var = Cnone;
    }
    switch (var) {
    case Cnone: break;
    case Cdep: dep = ival; break;
    case Carr: arr = ival; break;
    case Cscale: scale = ival; break;
    case Cdeplat: deplat = ival; break;
    case Cdeplon: deplon = ival; break;
    case Carrlat: arrlat = ival; break;
    case Carrlon: arrlon = ival; break;
    case Ctdep: tdep = ival; break;
    case Cttdep: ttdep = ival; break;
    case Cplushour: plushour = ival; break;
    case Cminhour: minhour = ival; break;
    case Clostop:  lostop = ival; break;
    case Chistop: histop = ival; break;

    case CminttAA: mkmintt(mintts,Airintbit,Airintbit,ival); break;
    case CminttAa: mkmintt(mintts,Airintbit,Airdombit,ival); break;
    case Cminttaa: mkmintt(mintts,Airdombit,Airdombit,ival); break;
    case CminttaA: mkmintt(mintts,Airdombit,Airintbit,ival); break;
    case CminttAx: mkmintt(mintts,Airintbit,Railbit|Busbit|Taxibit|Ferrybit,ival); break;
    case CminttxA: mkmintt(mintts,Railbit|Busbit|Taxibit|Ferrybit,Airintbit,ival); break;
    case Cminttax: mkmintt(mintts,Airdombit,Railbit|Busbit|Taxibit|Ferrybit,ival); break;
    case Cminttxa: mkmintt(mintts,Railbit|Busbit|Taxibit|Ferrybit,Airdombit,ival); break;

    case Cminttbx: mkmintt(mintts,Busbit,Railbit|Busbit|Taxibit|Ferrybit,ival); break;
    case Cminttxb: mkmintt(mintts,Railbit|Busbit|Taxibit|Ferrybit,Busbit,ival); break;
    case Cmintttt: mkmintt(mintts,Railbit,Railbit,ival); break;
    case Cminttxf: mkmintt(mintts,Railbit|Busbit|Taxibit|Ferrybit,Ferrybit,ival); break;
    case Cminttfx: mkmintt(mintts,Ferrybit,Railbit|Busbit|Taxibit|Ferrybit,ival); break;

    case Ccostperstop: costperstop = ival; break;
    case Csrcmode: srcmode = ival; break;
    case Cwalklimit: walklimit = ival; break;
    case Cwalkspeed: walkspeed = ival; break;
    case Csumwalklimit: sumwalklimit = ival; break;
    case Cnethistop: nethistop = ival; break;
    case Cutcofs: utcofs = ival; break;
    case Cdsputcofs: dsputcofs = ival; break;
    case Ctxmask: txmask = ival; break;
    case Ctlimit: tlimit = ival; break;
    case Cntop: ntop = ival; break;
    case Crepoptions: repoptions = ival; break;
    case Ctestiter: testiter = ival; break;
    }
  }

  if (req->alloced) {
    afree(req->buf,"client request");
    req->alloced = 0;
  }
  tlimit = min(tlimit,300);

  if (sumwalklimit < walklimit) {
    warn(msgtid,"max distance for single go walk %u above summed max %u",walklimit,sumwalklimit);
    sumwalklimit = walklimit;
  }
  if (txmask == 0) {
    warn(msgtid,"txmask %x",txmask);
    txmask = 0xff;
  } else if (txmask > 0xff) {
    warn(msgtid,"txmask %x",txmask);
    txmask = 0xff;
  }

  if (dep == hi32) {
    dep = geocode2(deplat,deplon,scale,0xff,&rep);
    if (dep == hi32) return error(msgtid,"no match for %u,%u",deplat,deplon);
  }
  if (arr == hi32) {
    arr = geocode2(arrlat,arrlon,scale,0xff,&rep);
    if (arr == hi32) return error(msgtid,"no match for %u,%u",arrlat,arrlon);
  }
  oclear(rep);

  if (dep > portcnt && dep - portcnt >= sportcnt) return error(msgtid,"dep %u not in %u member net",dep - portcnt,sportcnt);
  if (arr > portcnt && arr - portcnt >= sportcnt) return error(msgtid,"arr %u not in %u member net",arr - portcnt,sportcnt);

  if (dep == arr) warning(msgtid,"dep %u equal to arr",dep);

  if (ntop > Ntop) { warn(msgtid,"ntop %u above max %u",ntop,Ntop); ntop = Ntop; }
  else if (ntop == 0) { warn0(msgtid,"ntop zero"); ntop = 1; }

  if (tdep < Epoch) { warn(msgtid,"tdep %u below epoch %u",tdep,Epoch); tdep = Epoch; }
  else if (tdep > Era) { warn(msgtid,"tdep %u above era %u",tdep,Era); tdep = Era; }

  if (srcmode >= Srcmodecnt) { warn(msgtid,"srcmode %u above max %u",srcmode,Srcmodecnt); srcmode = Srchitime; }

  if (walkspeed == 0) { warn(msgtid,"walkspeed zero for distance \ag%u",walklimit); walkspeed = 1; }

  src->depttmin_cd = ttdep;
  src->deptmin_cd = tdep;
  src->utcofs12 = utcofs;
  src->dsputcofs12 = dsputcofs;
  src->plushour = plushour;
  src->minhour = minhour;
  src->nethistop = min(nethistop,histop);
  src->costperstop = costperstop;
  src->txmask = (ub1)txmask;
  src->limitfac = tlimit;
  src->srcmode = srcmode;
  src->ntop = ntop;

  src->walkspeed = max(m2geo(walkspeed),1);
  src->walklimit = m2geo(walklimit);
  src->sumwalklimit = m2geo(sumwalklimit);

  src->repoptions = repoptions;

  // invoke actual plan here
  info(msgtid,"plan %u to %u in %u to %u stop\as from %u.%u for +%u -%u hours",dep,arr,lostop,histop,tdep,ttdep,plushour,minhour);
  info(msgtid,"maxwalk %u speed %u costperstop %u utcofs %u %u txmask %x mode %u opts %x ntop %u",
    walklimit,walkspeed,costperstop,utcofs,dsputcofs,txmask,srcmode,repoptions,ntop);

  rv = plantrip(src,req->name,dep,arr,lostop,histop);

  // prepare reply
  rep.buf = rep.localbuf;
  if (rv) len = fmtstring(rep.localbuf,"reply plan %u-%u error code %d\n",dep,arr,rv);
  else if (src->reslen) {
    len = min(src->reslen,sizeof(rep.localbuf));
    errorcc(len < src->reslen,msgtid,"result truncated from %u to %u",src->reslen,len);
    memcpy(rep.localbuf,src->resbuf,len);
  } else len = fmtstring(rep.localbuf,"reply plan %u-%u : no trip found\n",dep,arr);
  vrb0(msgtid,"reply len %u",len);
  rep.len = len;

  rv |= setqentry(req,&rep,".rep");

  if (testiter == 0 || dep == arr) return rv;

  ub4 iter = 0;

  while (iter < testiter) {
    if (++arr == portcnt) {
      arr = 0;
      if (++dep == portcnt) dep = 0;
    }
    if (dep == arr) continue;
    iter++;
    rv = plantrip(src,req->name,dep,arr,lostop,histop);
    if (rv) return error(msgtid,"plantrip returned %d",rv);
  }

  ub4 iv,cnt,cumcnt = 0;

  cnt = src->notrips;
  info(msgtid|CC0,"%u of %u trips not found",cnt,testiter);
  info(msgtid,"max dur %lu msec for dep %u arr %u",src->querymaxdur / 1000,src->querymaxdep,src->querymaxarr);
  info(msgtid,"query times in msec for %u iters",testiter);
  for (iv = 0; iv < Elemcnt(src->querydurs); iv++) {
    cnt = src->querydurs[iv];
    cumcnt += cnt;
    infocc(cnt,msgtid,"%02u: %u %u",iv,cnt,cumcnt);
  }

  return 0;
}

static int updfares(gnet *net,ub4 *vals,ub4 valcnt)
{
  ub4 rrid = vals[0];
  ub4 dep = vals[1];
  ub4 arr = vals[2];
  ub4 t0 = vals[3];
  ub4 vndx = 4;
  ub4 rid,t,dt,mask,n;
  ub4 *rrid2rid = net->rrid2rid;
  ub4 hirrid = net->hirrid;
  struct route *rp;
  struct port *pdep,*parr,*ports = net->ports;
  ub4 portcnt = net->portcnt;
  ub4 hopcnt = net->hopcnt;
  ub4 *portsbyhop = net->portsbyhop;

  if (net->fareposcnt == 0) return warn(0,"no reserved routes to update for %u-%u",dep,arr);
  if (dep == arr) return error(0,"dep %u equals arr",dep);
  else if (dep >= portcnt) return error(0,"dep %u above %u",dep,portcnt);
  else if (arr >= portcnt) return error(0,"arr %u above %u",arr,portcnt);
  pdep = ports + dep;
  parr = ports + arr;
  info(0,"%u-%u %s to %s",dep,arr,pdep->name,parr->name);

  if (rrid > hirrid) return error(0,"rrid %u above max %u",rrid,hirrid);
  rid = rrid2rid[rrid];
  if (rid >= net->ridcnt) return error(0,"rid %u above max %u",rid,net->ridcnt);

  vrb0(0,"r.rid %u.%u t \ad%u",rrid,rid,t0);

  rp = net->routes + rid;
  if (rp->reserve == 0) return warn(0,"ignoring rrid %u for nonreserved route",rrid);
  if (rp->hopcnt == 0) return warn(0,"no hops on rrid %u",rrid);

  ub4 *ridhops,*ridhopbase = net->ridhopbase;
  ridhops = ridhopbase + rp->hop2pos;

  // get hop from rid,dep,arr. orgs in case of compound
  ub4 hopndx = 0,h1ndx = 0,h2ndx = 0;
  ub4 rhopcnt = rp->hopcnt;
  ub4 h,chop,hop1 = hi32,hop2 = hi32;

  while (hopndx < rhopcnt && (hop1 == hi32 || hop2 == hi32)) {
    h = rp->hops[hopndx];
    if (portsbyhop[h * 2] == dep) { hop1 = h; h1ndx = hopndx; }
    if (portsbyhop[h * 2 + 1] == arr) { hop2 = h;  h2ndx = hopndx; }
    hopndx++;
  }
  if (hop1 == hi32 || hop2 == hi32) return error(0,"no hop found for %u-%u",dep,arr);
  else if (hop1 >= hopcnt) return error(0,"invalid hop %u found for %u-%u",hop1,dep,arr);
  else if (hop2 >= hopcnt) return error(0,"invalid hop %u found for %u-%u",hop2,dep,arr);
  if (hop1 == hop2) chop = hop1;
  else chop = ridhops[h1ndx * rhopcnt + h2ndx];
  if (chop == hi32) return 1;

  info(0,"found hop %u,%u = %u",hop1,hop2,chop);

  while (vndx + 2 < valcnt) {
    dt = vals[vndx];
    mask = vals[vndx+1];
    vndx += 2;
    t = t0 + dt;
    vrb0(0,"dt %u t \ad%u mask %u",dt,t,mask);
    n = bitsinmask[mask & (Faregrp-1)];
    fareupd(net,rid,hop1,hop2,chop,t,mask,n,vals + vndx);
    vndx += n;
  }
  return 0;
}

#define Maxvals 1024
/* handle an update command
   fare availability:
     rid t (dt grpmask fare1 fare2 ..)+
     rid  = route id : rrid
     t = time in minutes since epoch
     dt = idem, relative to above
     grpmask is bitmap for each known fare group
 */
static int cmd_upd(struct myfile *req,ub4 seq)
{
  char c,*lp = req->buf;
  ub4 pos = 0,len = (ub4)req->len;
  ub4 valcnt,val,x;
  enum states { Out, Val0, Val1, Item, Fls } state;
  enum cmd { Upd_fare };
  ub4 vals[Maxvals];

  info(0,"update seq %u len %u",seq,len);

  if (len == 0) return 0;
  gnet *net = getnet();

  state = Out; valcnt = val = 0;
  while (pos < len) {
    c = lp[pos++];
    x = hexmap[(ub4)(c & 0x7f)];

//  info(0,"c %x x %x state %u",c,x,state);
    switch(state) {
    case Out:  if (x < 0x10) { val = x; state = Val1; }
               else if (x != 0xfe) state = Fls;
               break;
    case Val0: if (x < 0x10) { val = x; state = Val1; }
               else if (x == 0xfe) state = Item;
               else if (x != 0x20) state = Fls;
               break;
    case Val1: if (x < 0x10) val = (val << 4) + x;
               else if (x == 0x20) { vals[valcnt++] = val; state = Val0; }
               else if (x == 0xfe) state = Item;
               else state = Fls;
               break;

    case Fls:  if (x == 0xfe) state = Out; break;

    case Item: info(0,"%u vals",valcnt); break;
    }
    if (state == Item) {
      state = Out;
      info(0,"%u vals",valcnt);
      if (valcnt == 0) break;
      else if (vals[0] == Upd_fare && valcnt > 7) updfares(net,vals+1,valcnt-1);
      break;
    }
  }

  return 0;
}

struct planparm {
  int rv;
  ub4 tid;
  gnet *net;
  struct myfile *req;
  search *src;
};

// wrapper around cmd_plan, fork here
static void *start_plan(void *vp)
{
  struct planparm *pp = (struct planparm *)vp;
  struct myfile *preq = pp->req;
  struct myfile req;
  search *src = pp->src;
  gnet *net = pp->net;
  ub4 tid = pp->tid;

  int rv;

  threadstart(tid);
  ub4 msgtid = (tid << Tidshift) | Tidbit;
  src->msgtid = msgtid;

  req = *preq;
  if (preq->alloced) {
    req.buf = alloc0(preq->len,char,0);
    memcpy(req.buf,preq->buf,preq->len);
    info(msgtid,"alloc %lu req for tid %u",preq->len,tid);
  } else req.buf = req.localbuf;
  info(msgtid,"new plan in tid %u %lu",tid,preq->len);
  rv = cmd_plan(net,&req,src);
  info(msgtid,"new plan in tid %u",tid);
  if (preq->alloced) afree0(req.buf);
  pp->rv = rv;

  info(CC0|msgtid,"plan returned %d",rv);
  threadend(tid);

  return &pp->rv;
}

/* currently a directory queue based interface
 future plan :
  use a single local proxy on same system that interfaces here with sockets
  have at least a set of 2 servers, allow network rebuild
  remote client interfaces to proxy at e.g. port 80
  proxy on behalf of client to here, synchronously. proxy forks per request
  server accepts one conn only, proxy knows list of servers and iterates
  have directory-based queue for real-time status updates only
  status updates synchronously, rely on having a set of servers
 */
int serverloop(void)
{
  const char *querydir = globs.querydir;
  struct myfile *preq;
  static struct myfile req;
  int prv = 1,rv = 1;
  enum Cmds cmd = Cmd_nil;
  ub4 prvseq = 0,seq = 0,useq = 0,iter = 0;
  char c;
  const char *region = "glob"; // todo
  int do_thread;
  struct network *net = getnet();
  ub4 tid,tidcnt = globs.tidcnt;

  static search src;
  search *srcs = alloc0(Nthread,search,0);
  struct myfile *reqs = alloc0(Nthread,struct myfile,0);
  struct planparm pp;

  oclear(req);
  oclear(src);
  pp.src = &src;
  pp.net = net;

  inisrc(net,&src,"init",0);
  for (tid = 0; tid < tidcnt; tid++) inisrc(net,srcs + tid,"init",0);

  msgsum(1);
  show_version();

  info0(0,"use plantrip to access the server");
  info(Emp,"entering server loop for id %u",globs.serverid);

  do {
    infovrb(seq > prvseq,0,"wait for new cmd %u",seq);

    if (req.alloced) afree(req.buf,"client request");
    oclear(req);
    rv = getqentry(querydir,&req,region,".sub");
    if (rv) { warn(0,"return on qentry %d",rv); break; }

    prvseq = seq;

    if (req.direxist == 0) osmillisleep(2000);
    else if (req.exist == 0) {
      joinanythread();
      if ((iter % 200) == 0) loadplans();
      osmillisleep(10);  // for linux only we may use inotify instead
      iter++;
    } else {
      info(0,"new client entry %s",req.name);
      do_thread = 1;
      c = req.name[req.basename];
      switch(c) {
      case 's': cmd = Cmd_stop; break;
      case 'p': cmd = Cmd_plan; break;
      case 'P': cmd = Cmd_plan; do_thread = 0; break;
      case 'g': cmd = Cmd_geo; do_thread = 0; break;
      case 'u': cmd = Cmd_upd; break;
      default: info(0,"unknown command '%c'",c);
      }
      if (cmd == Cmd_plan) {
        src.cmdseq = seq++;
        for (tid = 0; tid < tidcnt; tid++) {
          if (globs.tids[tid] == 0) break;
        }
        if (tid == tidcnt) do_thread = 0;

        if (do_thread) {
          pp.tid = tid;
          pp.src = srcs + tid;
          preq = pp.req = reqs + tid;

          if (preq->alloced) afree0(preq);

          *preq = req;
          if (preq->alloced) {
            preq->buf = alloc0(preq->len,char,0);
            memcpy(preq->buf,req.buf,preq->len);
            info(0,"alloc %lu req for tid %u",preq->len,tid);
          } else preq->buf = preq->localbuf;
          prv = newthread(tid,start_plan,&pp);
          if (prv) return 1;
        } else {
          // clriters();
          rv = cmd_plan(net,&req,&src);
        }
      } else if (cmd == Cmd_upd) {
        prv = cmd_upd(&req,useq);
        if (prv) info(0,"update returned %d",prv);
        useq++;
      } else if (cmd == Cmd_geo) {
        prv = cmd_geo(&req);
        if (prv) info(0,"geo returned %d",prv);
      }
    }
    if (globs.once && seq) {
      info(0,"leaving server loop for id %u on once",globs.serverid);
      break;
    }
  } while (cmd != Cmd_stop && globs.sigint == 0);

  info(0,"leaving server loop for id %u: stop %u int %u",globs.serverid,cmd == Cmd_stop,globs.sigint);

  error(CC0,"\ah%u search errors",src.errcnt);

  return rv;
}

void iniserver(void)
{
  msgfile = setmsgfile(__FILE__);
  iniassert();
  mkhexmap();
  mkbitmask();
  mkidmap();
}
