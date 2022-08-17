// netbase.c - base network with primary data

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2016 Joris van der Geer.
 */

/* Functions to setup or create a base network */

#include <string.h>
#include <stdarg.h>

#include "base.h"
#include "cfg.h"
#include "mem.h"
#include "math.h"

static ub4 msgfile;
#include "msg.h"

#include "time.h"
#include "util.h"
#include "netbase.h"
#include "netio.h"
#include "event.h"

static const ub4 daymin = 60 * 24;   // convenience

// holds everything primary. in contrast, net.h contains derived info
static netbase basenet;

static const ub4 hop2watch = hi32; // tmp debug provision
static const ub4 tid2watch = hi32;
static const ub4 rrid2watch = hi32;

static const ub4 Bdtidlim = (1U << Bdtidbits) - 1;

netbase *getnetbase(void) { return &basenet; }

#include "watch.h"

/* merge services and time ranges for each route
 input is a list of gtfs-style entries like 'each wed dep 11.33 arr 11.36 valid 20140901-20141231'
 output is list of <time,trip> tuples over whole period.

 actual entry is tripid ( flightno in air) and duration
 input times are in localtime, output times are in minutes UTC since Epoch
 */

static const ub4 maxev4hop = 6 * 30 * 24 * 20;
static const ub8 maxzev = 3UL * 1024 * 1024 * 1024;  // todo arbitrary

static const char *kindnames[] = { "?","air int","air dom","rail","bus","ferry","taxi","walk" };

static char *fmtrip(char *buf,ub4 buflen,ub4 tripno)
{
  if (tripno == 0) { *buf = 0; return buf; }
  ub4 fltno1 = tripno & hi16;
  ub4 alcode1 = tripno >> 24;
  ub4 alcode2 = (tripno >> 16) & 0xff;
  if (alcode1 < 'A' || alcode1 > 'Z') alcode1 = '?';
  if (alcode2 < 'A' || alcode2 > 'Z') alcode2 = '?';
  mysnprintf(buf,0,buflen,"%c%c%u",alcode1,alcode2,fltno1);
  return buf;
}

static int prepbase(void)
{
  struct portbase *ports,*pdep,*parr,*pp;
  struct hopbase *hp1,*hp2,*rawhp,*rawhops;
  struct sidbase *sids,*sp;
  ub4 portcnt,hopcnt,sidcnt,ridcnt,rawhopcnt;
  ub4 dep,arr,srdep,srarr,srda,dsubcnt,asubcnt;
  ub4 hop,rhop,rawhop;
  const char *dname,*aname,*hname;

  rawhops = basenet.hops;
  rawhopcnt = basenet.hopcnt;

  portcnt = basenet.portcnt;
  ports = basenet.ports;
  sids = basenet.sids;
  sidcnt = basenet.sidcnt;
  ridcnt = basenet.ridcnt;

  ub4 gt0 = basenet.t0;
  ub4 gt1 = basenet.t1;
  error_le(gt1,gt0);
  ub4 gdt = gt1 - gt0;
  info(0,"gross time range \ad%u - \ad%u",gt0,gt1);

  ub4 *tbp,*timesbase = basenet.timesbase;
  ub4 tndx,vndx,timecnt,timespos,evcnt,cnt;
  ub4 sid,rsid,tid,rtid,rid,rrid,tripno;
  ub4 tdep,tarr,tdeprep,trepstart,trepend,tripseq,tdepsec,tarrsec;
  ub4 trepivsec,trepstartsec,trependsec,trepiv;
  ub4 chcnt,i;
  ub4 t0,t1,ht0,ht1,hdt,tdays,mapofs;
  ub8 cumevcnt = 0,evofs = 0,cumfevcnt = 0,cumtdays = 0;
  ub4 evhops = 0;
  ub4 dur,lodur,hidur,midur,prvdur,duracc,sumdur,eqdur = 0,accdur = 0;
  ub4 sumtimes = 0;
  ub4 x;

  error_zz(rawhopcnt,portcnt);
  error_zz(ridcnt,sidcnt);

  info(0,"preparing %u base hops in \ad%u - \ad%u",rawhopcnt,gt0,gt1);

  int do_chkev = (rawhopcnt < 50000);
  rsid2logcnt = getwatchitems("rsid",rsids2log,Elemcnt(rsids2log));
  hop2logcnt = getwatchitems("hop",hops2log,Elemcnt(hops2log));
  rsidlog(hi32,"%c",0);

  ? struct hopbase *hp,*hops = alloc(rawhopcnt,struct hopbase,0,"base hops",rawhopcnt);

  // workspace to expand single time
  ub4 xtimelen = gdt + 3 * daymin;
  ub8 *xp = talloc(xtimelen,ub8,0xff,"time xmap",gdt);
  ub1 *xpacc = talloc((xtimelen >> Baccshift) + 2,ub1,0,"time acc",gdt);

  // store events here
  block *eventmem;

  struct timepatbase *tp;
  struct routebase *rp,*routes = basenet.routes;
  ub1 *daymap,*sidmaps = basenet.sidmaps;

  struct eta eta;

  ub4 cumhoprefs = basenet.chainhopcnt;
  ub4 cumhoprefs2 = 0;
  struct chainbase *cp,*chains = basenet.chains;

  ub8 *chip,*chainidxs = talloc(cumhoprefs,ub8,0,"chain idx",cumhoprefs);
  struct chainhopbase *chp,*chp2,*chainhops = talloc(cumhoprefs,struct chainhopbase,0,"chain hops",cumhoprefs);

  ub4 chain;
  ub4 rawchaincnt = basenet.rawchaincnt;
  ub4 hirrid = basenet.hirrid;

  ub4 *tid2rtid = basenet.tid2rtid;

  double fdist;
  ub4 dist;
  char desc[512];
  int dbg = 0;

  error_z(rawchaincnt,0);

  ub4 ofs = 0,chainofs = 0;
  for (chain = 0; chain < rawchaincnt; chain++) {
    cp = chains + chain;
    cp->hopofs = chainofs;
    error_ge(chainofs,hi32 - cp->hoprefs);
    chainofs += cp->hoprefs;
    rid = cp->rid;
    if (rid == hi32) return error(0,"chain %u has no rid",chain);
    error_ge(rid,ridcnt);
    rp = routes + rid;
    cnt = rp->hopcnt;
    error_z(cnt,chain);
    infovrb(chain == tid2watch,0,"rid %u cnt %u",rid,cnt);
    cp->rhopcnt = cnt;
    error_ge(ofs,hi32 - cnt);
    ofs += cnt;
  }
  error_ne(chainofs,cumhoprefs);

  for (hop = 0; hop < hopcnt; hop++) {
    hp = hops + hop;
    if (hp->dep == hp->arr) return error(0,"hop %u is dummy",hop);
    hp->evofs = cumevcnt;
    cumevcnt += hp->evcnt;
  }

  // assign rid-relative hops
  // not needed if sorted
#if 0
  for (hop = 0; hop < hopcnt; hop++) {
    hp = hops + hop;
    if (hp->dep == hp->arr) return error(0,"hop %u is dummy",hop);
    hp->rhop = hi32;
    rid = hp->rid;
    if (rid == hi32) return error(0,"hop %u has no rid",hop);
    error_ge(rid,ridcnt);
    rp = routes + rid;
    rhop = rp->hopndx;
    if (rhop > 348) {
      info(0,"hop %u rid %u index %u on %s",hop,rid,rhop,rp->name);
    }
    hp->rhop = rhop;
    rp->hopndx = rhop + 1;
  }
  for (rid = 0; rid < ridcnt; rid++) {
    rp = routes + rid;
    warncc(rp->hopndx != rp->hopcnt,0,"index %u cnt %u",rp->hopndx,rp->hopcnt);
  }
  for (chain = 0; chain < rawchaincnt; chain++) {
    cp = chains + chain;
    rid = cp->rid;
    rp = routes + rid;
    error_ne(rp->hopcnt,cp->rhopcnt);
  }
  for (hop = 0; hop < hopcnt; hop++) {
    hp = hops + hop;
    rhop = hp->rhop;
    rid = hp->rid;
    rp = routes + rid;
    error_ge(rhop,rp->hopcnt);
  }
#endif

  dbg = 0;

  int do_chkxtime = (rawhopcnt < 1000);

  char ckind;
  ub4 lolim,hilim;
  ub4 lotripno,hitripno;
  ub8 speed;
  ub4 hispeeds[Kindcntb],lospeeds[Kindcntb],hihops[Kindcntb],lohops[Kindcntb];
  enum txbkind kind;
  char tripfmt[64];
  ub4 ftriplen = (ub4)sizeof(tripfmt);
static  ub4 cntbins[65536];
  ub4 cnthvbin = 0,cnthibin = Elemcnt(cntbins)-1;

  for (kind = 0; kind < Kindcntb; kind++) {
    hispeeds[kind] = 0;
    lospeeds[kind] = hi32;
    hihops[kind] = lohops[kind] = hi32;
  }

  ub4 period0 = globs.periodt0 * 1440;
  ub4 period1 = globs.periodt1 * 1440;
  ub4 st0 = globs.pat0 * 1440;
  ub4 st1 = globs.pat1 * 1440;
  ub4 nt0 = max(period0,gt0);
  ub4 nt1 = period1 ? min(period1,gt1) : gt1;
  error_le(nt1,nt0);
  ub4 ldt,ndt = (nt1 - nt0) / daymin;
  ndt++;

  // net outer range
  ub4 agt0,tt0 = basenet.tt0 = hi32;
  ub4 agt1,tt1 = basenet.tt1 = 0;

  ub4 aid,agencycnt = basenet.agencycnt;

#define Agcntbins 64
  ub4 agcnthibin = Agcntbins - 1;
  ub4 *agcntp,*agcntbins = alloc(agencycnt * Agcntbins,ub4,0,"net evcntstats",0);

  ub4 *agspnp,*agspnbins = alloc(agencycnt * ndt,ub4,0,"net evspnstats",0);
  ub4 *aghops = alloc(agencycnt,ub4,0xff,"net aghops",0);

  ub4 *agtt0 = alloc(agencycnt,ub4,0xff,"net agtt0",0);
  ub4 *agtt1 = alloc(agencycnt,ub4,0,"net agtt1",0);

  ub4 eqhop,invcnt = 0,invtt = 0,invte = 0,noevcnt = 0,ev1cnt = 0,filtercnt = 0,colocnt = 0,eqhopcnt = 0;
  ub4 gtpatcnt = 0,ltpatcnt = 0;

#if 0
  // pass 1: expand time entries, determine memuse and assign chains
  hop = 0;
  for (rawhop = 0; rawhop < rawhopcnt; rawhop++) {

    if (progress(&eta,"hop %u of %u in pass 1, \ah%lu events",rawhop,rawhopcnt,cumevcnt)) return 1;

    rawhp = rawhops + rawhop;

    hp = hops + hop;
    *hp = *rawhp;
    dbg = (hop == 327);

    ckind = 'x';
    switch(hp->kind) {
      case Airintb: ckind = 'A'; break;
      case Airdomb: ckind = 'a'; break;
      case Railb:  ckind = 'r'; break;
      case Busb:   ckind = 'b'; break;
      case Taxib:  ckind = 't'; break;
      case Ferryb: ckind = 'f'; break;
      case Walkb: ckind = 'w'; break;
      case Unknownb: case Kindcntb: ckind = 'x'; break;
    }

    if (hop == rawhop) msgprefix(0,"%chop %u",ckind,hop);
    else msgprefix(0,"%chop %u,%u",ckind,hop,rawhop);
    eqhop = 0;

    dep = hp->dep;
    arr = hp->arr;
    error_ge(dep,portcnt);
    error_ge(arr,portcnt);
    error_eq(dep,arr);
    pdep = ports + dep;
    parr = ports + arr;

    dname = pdep->iname;
    aname = parr->name;
    hname = hp->iname;
    dsubcnt = pdep->subcnt;
    asubcnt = parr->subcnt;

    fmtstring(desc,"%.128s to %.128s %.128s",dname,aname,hname);
    infocc(dbg,Notty,"%u-%u %s-%s",dep,arr,dname,aname);

    if (pdep->lat && pdep->lat == parr->lat && pdep->lon && pdep->lon == parr->lon) {
      colocnt++;
      warn(Iter,"ports %u-%u coloc %u,%u %.128s",dep,arr,pdep->lat,pdep->lon,desc);
      dist = 1;
    } else if (pdep->lat == 0 || pdep->lon == 0 || parr->lat == 0 || parr->lon == 0) {
      warn(Iter,"ports %u-%u no coords %s to %s",dep,arr,dname,aname);
      dist = 50000;
    } else {
      fdist = geodist(pdep->rlat,pdep->rlon,parr->rlat,parr->rlon,pdep->name);
      if (fdist < 1) warning(Iter,"port %u-%u distance %e for latlon %u,%u-%u,%u %.128s",dep,arr,fdist,pdep->lat,pdep->lon,parr->lat,parr->lon,desc);
      else if (fdist > 1600000) warn(0,"port %u-%u distance \ag%u for latlon %u,%u-%u,%u %.128s",dep,arr,(ub4)fdist,pdep->lat,pdep->lon,parr->lat,parr->lon,desc);
      dist = (ub4)(fdist + 0.5);
    }
    hp->dist = max(dist,1);

    if (hp->t1 <= hp->t0) { warn(0,"skip hop %u on t %u %u %.128s",hop,hp->t0,hp->t1,desc); invtt++; continue; }

    rrid = hp->rrid;
    rid = hp->rid;
    error_eq(rid,hi32);
    error_ge(rid,ridcnt);
    rp = routes + rid;
    aid = rp->aid;
    error_ge(aid,agencycnt);
    if (aghops[aid] == hi32) aghops[aid] = hop;

    if (rrid == rrid2watch || dbg) info(Notty,"r.rid %u.%u %s to %s route %s",rrid,rid,pdep->name,parr->name,hp->name);

    hoplog(hop,0,"rrid %x %u-%u %s to %s",rrid,dep,arr,pdep->name,parr->name);

    // times
    timespos = hp->timespos;
    timecnt = hp->timecnt;
    if (timecnt == 0) return error0(0,"no time entries");
    bound(&basenet.timesmem,(timespos + timecnt - 1) * Tentries,ub4);
    tbp = timesbase + timespos * Tentries;
    evcnt = 0;
    error_le(hp->t1,hp->t0);
    hdt = hp->t1 - gt0 + 1 * daymin;
    error_ge(hdt,xtimelen);

    ht0 = hi32; ht1 = 0;
    tp = &hp->tp;
    tp->hop = hop;
    tp->t0 = tp->t1 = 0;
    tp->gt0 = gt0;

    for (i = 0; do_chkxtime && i < xtimelen; i++) {
      x = xp[i] & hi32;
      warncc(x != hi32,0,"hop %u i %u x %x",hop,i,x);
    }

    tp->t0 = hi32;
    lodur = hi32; hidur = sumdur = lotripno = hitripno = 0;
    for (tndx = 0; tndx < timecnt; tndx++) {
      sid = tbp[Tesid];

      tid = tbp[Tetid];
      error_ge(tid,rawchaincnt);
      rtid = tid2rtid[tid];

      tripno = tbp[Tetripno];

      tdepsec = tbp[Tetdep];
      tarrsec = tbp[Tetarr];
      trepivsec = tbp[Terepiv];
      trepstartsec = tbp[Terepstart];
      trependsec = tbp[Terepend];

      tripseq = tbp[Teseq];
      srdep = tbp[Tesdep];
      srarr = tbp[Tesarr];

      error_lt(tarrsec,tdepsec);

      if (srdep != hi32) {
        error_ge(srdep,dsubcnt);
      }
      if (srarr != hi32) {
        error_ge(srarr,asubcnt);
      }

      tdep = (tdepsec + 30) / 60;
      tarr = (tarrsec + 30) / 60;
      trepiv = (trepivsec + 30) / 60;
      trepstart = (trepstartsec + 30) / 60;
      trepend = (trependsec + 30) / 60;

//    infocc(tdepsec == 0 && tarrsec < 600,0,"tdep 0 for tarr %u %s %s %s",tarr,dname,aname,hp->name);
//    infocc(tarrsec == 0,0,"tarr 0 for tdep %u %s %s %s",tdep,dname,aname,hp->name);

      if (utcofsa < utcofsd) {
        tarrd = tarr + (utcofsd - utcofsa);
      } else {
        error_lt(tarr,utcofsa - utcofsd);
        tarrd = tarr - (utcofsa - utcofsd);
      }

      error_lt(tarrd,tdep);
      dur = tarrd - tdep;
      if (tarrsec - tdepsec < 60 && dist > 10) { // todo fr/ter fr/transil
        info(Iter|Notty|V0,"dur 0 tdep %u tarr %u rtid %u %.128s",tdepsec,tarrsec,rtid,desc);
        info(V0,"dur 0 tdep %u tarr %u rtid %u %.128s",tdepsec,tarrsec,rtid,desc);
      }

      // infocc(hop == 7649 || hop == 7650,0,"tid %u seq %u td \ad%u ta \ad%u",tid,tripseq,tdep,tarr);

      if (dur < lodur) { lodur = dur; lotripno = tripno; }
      if (dur > hidur) { hidur = dur; hitripno = tripno; }
      sumdur += dur;
      error_ge(sid,sidcnt);
      sp = sids + sid;
      if (sp->valid == 0) {
        warn(0,"skip invalid sid %s",sp->name);
        tbp[0] = sidcnt; // disable for next pass
        tbp += Tentries;
        continue;
      }

      rsid = sp->rsid;

      t0 = sp->t0;
      t1 = sp->t1;

      error_le(t1,t0);

      ht0 = min(ht0,t0);
      ht1 = max(ht1,t1);
      tp->utcofs = sp->utcofs;
      mapofs = sp->mapofs;
      daymap = sidmaps + mapofs;

      // todo: create chksum, detect duplicates
      tdeprep = tdep | (trepiv << 16);
      cnt = fillxtime(&basenet,hop,tp,xp,xpacc,xtimelen,gt0,sp,daymap,tdeprep,trepstart,trepend,tid,desc);
      hoplog(hop,0,"r.tid %u.%u rsid %u \ad%u \ad%u td \ad%u ta \ad%u %u events",rtid,tid,rsid,t0,t1,tdep,tarr,cnt);
      infocc(dbg || hop == 41,V0,"r.tid %u.%u rsid %u \ad%u \ad%u td \ad%u ta \ad%u %u evs %s %s",rtid,tid,rsid,t0,t1,tdep,tarr,cnt,dname,aname);
      if (cnt == 0) {
        msgopt("showdup"); info(0,"tid %u r.sid %u.%u dow %x %s  \ad%u \ad%u dep \ad%u arr \ad%u no events",
          tid,rsid,sid,sp->dow,sp->dowstr,t0,t1,tdep,tarr);

        tbp[Tesid] = sidcnt; // disable for next pass
        tbp += Tentries;
        continue;
      }

      // create chains: list of hops per trip, sort on tripseq later
      error_ge(tid,rawchaincnt);

      srdep &= 0xff;
      srda = (srdep << 8) | (srarr & 0xff);

      rhop = hp->rhop;
      error_ge(rhop,rp->hopcnt);
      cp = chains + tid;
      error_ge_cc(rhop,cp->rhopcnt,"rid %u/%u cnt %u of %u",rid,cp->rid,cp->rhopcnt,rp->hopcnt);
      cp->tripno = tripno;
      rtid = cp->rtid;
      chip = chainidxs + cp->hopofs;
      chcnt = cp->hopcnt;
      ofs = cp->hopofs;
      error_ge(ofs + chcnt,cumhoprefs);
      chp = chainhops + ofs + chcnt;
      pp = ports + cp->dep;
      error_z_cc(tripseq,"time index %u of %u",tndx,timecnt);
      error_ge(chcnt,cp->hoprefs);

      vrbcc(dbg,0,"pos %u tdep %u",chcnt,tdep);
      if (chcnt == 0) {
        chip[0] = (ub8)tripseq << 32;
        error_z(chip[0],tid);
        chp->hop = hop;
        chp->chain = tid;
        chp->tdep = tdep;
        chp->tarr = tarr;
        chp->srda = srda;
        chp->seq = tripseq;
        cp->rrid = rrid;
        cp->rid = rid;
        cp->dep = dep;
        cp->hopcnt = 1;
        cp->lotdep = cp->hitdep = tdep;
        cp->lotarr = cp->hitarr = tarr;
        cp->lotdhop = cp->hitahop = hop;
        cumhoprefs2++;
        if (tid == tid2watch) {
          info(0,"r.rid %u.%u tid %u rhop %u at 0 td %u ta %u seq %u",rrid,rid,tid,rhop,tdep,tarr,tripseq);
          info(0,"sub %x %.24s to %.24s",srda,dname,aname);
        }
      } else {
        if (cp->rrid != rrid) warning(0,"hop %u tid %x on route %u vs %u",hop,tid,rrid,cp->rrid);
        chp2 = chainhops + ofs;
        for (i = 0; i < chcnt; i++) {
          if (chp2[i].hop == hop) { // todo loops (re-visits) in chain
            eqhop = 1;
            info(Notty|Iter|V0,"r.rid %u.%u r.tid %u.%u equal hop %u td \at%u vs \at%u at %u %s to %s start %s %s",rrid,rid,rtid,tid,hop,tdep,chp2[i].tdep,i,pdep->name,parr->name,pp->name,hp->name);
            break;
          } else if ( (chip[i] >> 32) == tripseq) {
            warn(0,"rrid %x tid %u skip equal seq %u at %u %s to %s start %s",rrid,tid,tripseq,i,pdep->name,parr->name,pp->name);
            break;
          }
        }
        if (i == chcnt) {
          if (tid == tid2watch || hop == hop2watch) {
            info(Notty|Noiter,"add hop %u tid %u at %u td \ad%u ta \ad%u %s to %s",hop,tid,i,tdep,tarr,dname,aname);
          }
          chip[chcnt] = chcnt | ((ub8)tripseq << 32);
          chp->hop = hop;
          chp->chain = tid;
          chp->tdep = tdep;
          chp->tarr = tarr;
          chp->srda = srda;
          chp->seq = tripseq;
          error_ge(chcnt,cp->hoprefs);
          error_ovf(chcnt,ub2);
          cp->hopcnt = chcnt + 1;
          if (tdep < cp->lotdep) { cp->lotdep = tdep; cp->lotdhop = hop; }
          cp->lotarr = min(cp->lotarr,tarr);
          cp->hitdep = max(cp->hitdep,tarr);
          if (tarr > cp->hitarr) { cp->hitarr = tarr; cp->hitahop = hop; }
          cumhoprefs2++;
          if (tid == tid2watch) {
            info(0,"r.rid %u.%u tid %u rhop %u at %u td %u ta %u seq %u",rrid,rid,tid,rhop,i,tdep,tarr,tripseq);
            info(0,"sub %x %.24s to %.24s",srda,pdep->name,parr->name);
          }
        }
      }

      evcnt += cnt;
      tp->evcnt = evcnt;
      sumdur += (dur * cnt);
      if (evcnt > maxev4hop) {
        warning(0,"hop %u exceeds event max %u %s",hop,maxev4hop,hp->name);
        hp->timecnt = tndx;
        break;
      }
      tbp += Tentries;
    } // each time entry

    agcntp = agcntbins + aid * Agcntbins;
    agcntp[min(evcnt,agcnthibin)]++;

    if (eqhop) eqhopcnt++;

    if (evcnt == 0) {
      return error(0,"hop %u no events for %u time entries, %u dup %s",rawhop,timecnt,hp->dupevcnt,hp->name);
      tp->t0 = min(tp->t0,tp->t1);
      noevcnt++;
      // continue;
    }

    error_lt(tp->t1,tp->t0);

    // obtain net date ranges
    agt0 = tp->t0 + gt0;
    agt1 = tp->t1 + gt0;
    tt0 = min(tt0,agt0);
    tt1 = max(tt1,agt1);
    if (tt0 < basenet.t0) return error(0,"net start date \ad%u before gross \ad%u %s",tt0,basenet.t0,hp->name);
    if (tt1 > basenet.t1) return error(0,"net end date \ad%u after gross \ad%u %s",tt1,basenet.t1,hp->name);

    agtt0[aid] = min(agtt0[aid],agt0);
    agtt1[aid] = max(agtt1[aid],agt1);

    ldt = (tp->t1 - tp->t0) / daymin;

    agspnp = agspnbins + aid * ndt;
    agspnp[min(ldt,ndt-1)]++;

    lolim = 1; hilim = 100;
    kind = hp->kind;
    switch(kind) {
      case Airintb: case Airdomb: lolim = 100; hilim = 1000; break;
      case Railb: lolim = 1; hilim = 300; break;
      case Busb: case Taxib: lolim = 2; hilim = 150; break;
      case Ferryb: lolim = 3; hilim = 50; break;
      case Unknownb: case Walkb: case Kindcntb: lolim = 1; hilim = 100; break;
    }

    warncc(lodur == 0 && dist > 200,Iter|Notty,"dur %u-%u dist %u for route %s %s to %s %s",lodur,hidur,dist,rp->name,dname,aname,fmtrip(tripfmt,ftriplen,lotripno));

    // hi speed
    speed = max(dist,1) / max(lodur,1);  // 10 m / min
    speed = (speed * 60) / 100;
    infocc(lodur > 1 && speed < lolim,V0,"speed %lu below %u for %s to %s %u %u %s",speed,lolim,dname,aname,dist,lodur,fmtrip(tripfmt,ftriplen,lotripno));
    infocc(lodur > 1 && speed > hilim,V0,"speed %lu above %u for %s to %s %u %u %s",speed,hilim,dname,aname,dist,lodur,fmtrip(tripfmt,ftriplen,hitripno));

    if (speed > hispeeds[kind]) { hispeeds[kind] = (ub4)speed; hihops[kind] = hop; }

    // lo speed
    speed = max(dist,1) / max(hidur,1);  // 10 m / min
    speed = (speed * 60) / 100;
    infocc(hidur > 1 && speed < lolim,V0,"speed %lu below %u for %s to %s %u %u %s",speed,lolim,dname,aname,dist,hidur,fmtrip(tripfmt,ftriplen,lotripno));
    infocc(hidur > 1 && speed > hilim,V0,"speed %lu above %u for %s to %s %u %u %s",speed,hilim,dname,aname,dist,hidur,fmtrip(tripfmt,ftriplen,hitripno));

    if (speed < lospeeds[kind]) { lospeeds[kind] = (ub4)speed; lohops[kind] = hop; }

    tp->avgdur = sumdur / evcnt;

    tp->evcnt = cnt = evcnt;
    if (period0 > agt0 || period1 < agt1) {
      warn(Iter,"event filter on \ad%u - \ad%u for \ad%u - \ad%u",period0,period1,agt0,agt1);
      cnt = filterxtime(tp,xp,xpacc,xtimelen,period0,period1);
      if (cnt == 0) {
        return error(0,"filtered %u events to 0",hp->evcnt);
//        tp->t0 = min(tp->t0,tp->t1);
//        clearxtime(tp,xp,xpacc,xtimelen);
//        filtercnt++;
//        continue;
      }
    }

    error_gt(cnt,evcnt,0);
    tp->evcnt = cnt;
    sumtimes += cnt;
    // info(Notty|Iter,"evcnt %u cnt %u",evcnt,cnt);
    evcnt = cnt;

    clearxtime(tp,xp,xpacc,xtimelen);

    if (cnt == 1) {
      info(Notty|Iter,"1 event \ad%u %u-%u rrid %u %s %s to %s",tp->t0 + gt0,dep,arr,rrid,rp->name,dname,aname);
      ev1cnt++;
    }

    evhops++;
    infovrb(dbg,0,"final date range \ad%u-\ad%u %s",tp->t0 + gt0,tp->t1 + gt0,hp->name);
    infocc(tp->t1 - tp->t0 < 1440 * 7,Iter|Notty|V0,"%u events range \ad%u-\ad%u route %s %s",cnt,tp->t0 + gt0,tp->t1 + gt0,rp->name,hp->name);

    pdep->ndep++;
    parr->narr++;

    lodur = min(lodur,hidur);
    tp->lodur = lodur;
    tp->hidur = hidur;

    duracc = 15;
    switch (hp->kind) {
      case Airdomb:  duracc = 15; break;
      case Airintb:  duracc = 30; break;
      case Railb: if (lodur > 12 * 60) duracc = 10; else duracc = 2; break;
      case Busb:  if (lodur > 2 * 60) duracc = 10; else duracc = 5; break;
      case Ferryb: duracc = 10; break;
      case Taxib: duracc = 10; break;
      case Walkb: duracc = 5; break;
      case Unknownb: duracc = 15; break;
      case Kindcntb: duracc = 15; break;
    }

    if (lodur == hidur) {
      tp->midur = hidur;
      eqdur++;
    } else if (hidur - lodur <= duracc) {
      tp->midur = hidur + lodur / 2;
      accdur++;
    } else if (hidur - lodur > 60 * 12) {
      warn(Iter,"duration %u-%u %s",lodur,hidur,hp->name);
      tp->midur = hidur + lodur / 2;
    } else if (hidur - lodur > duracc * 2) {
      info(Iter|V0,"duration %u-%u %s",lodur,hidur,hp->name);
      tp->midur = hidur + lodur / 2;
    }
    tp->duracc = duracc;

    if (hp->t0 != ht0) error(Exit,"t0 \ad%u vs \ad%u",hp->t0,ht0);

    if (tp->t0 + gt0 > st1) {
      infocc(globs.maxstops,Iter,"t0 \ad%u after sample end \ad%u",tp->t0 + gt0,st1);
      gtpatcnt++;
    } else if (tp->t1 + gt0 < st0) {
      info(Iter,"t1 \ad%u before sample start \ad%u",tp->t1 + gt0,st0);
      ltpatcnt++;
    }

    error_ne(hp->t0,ht0);
    ht1 += daymin;  // make end date exclusive
    error_ne(hp->t1,ht1);

    hp->evcnt = evcnt;
    error_ne(evcnt,tp->evcnt);

    if (hop == hop2watch) showxtime(tp,xp,xtimelen);

    if (tp->t0 > tp->t1) {
      warning(0,"hop %u t0 %u t1 %u for %u events",hop,tp->t0,tp->t1,evcnt);
      tp->t0 = ht0;
      tp->t1 = ht1;
    } else tp->t1++;
    tdays = (tp->t1 - tp->t0) / daymin + 1;
    cumtdays += tdays;

    if (cumevcnt + evcnt > maxzev) {
      warning(0,"hop %u: exceeding total event max \ah%lu %s",hop,maxzev,hp->name);
      break;
    }

    infovrb(dbg,0,"hop %u \ah%u time events %s",hop,evcnt,hp->name);
    cumevcnt += evcnt;
    hp->evcnt = evcnt;

    if (rp->reserve) cumfevcnt += evcnt;

    cntbins[min(evcnt,cnthibin)]++;
    hop++;
    error_gt(hop,rawhopcnt,0);
  }
  msgprefix(0,NULL);

  error_z(cumevcnt,0);
  hopcnt = hop;

  if (hopcnt == rawhopcnt) info(Emp,"\ah%u hops",hopcnt);
  else info(Emp,"\ah%u from \ah%u hops: %u no events",hopcnt,rawhopcnt,rawhopcnt - hopcnt);

  trimblock(&basenet.hopmem,0,struct hopbase);
  basenet.hopcnt = hopcnt;
  basenet.hops = hops;
#endif

  info(Emp,"\ah%lu org time events \ah%lu fare points",cumevcnt,cumfevcnt);
  info(0,"\ah%u org chainhops to \ah%u",cumhoprefs,cumhoprefs2);

  if (tt1 <= tt0) return error(0,"no net period \ad%u",tt0);
  info(Emp,"overall net period \ad%u - \ad%u",tt0,tt1);
  info(0,"%u routes",ridcnt);

  if (evhops < hopcnt) {
    info(0,"%u of %u hops without time events",hopcnt - evhops,hopcnt);
    info(0,"  %u inv %u tt %u te %u noev %u filter",invcnt,invtt,invte,noevcnt,filtercnt);
    if (evhops * 2 < hopcnt) return error(0,"%u of %u hops without time events",hopcnt - evhops,hopcnt);
  }
  info(CC0,"%u hop\as with 1 event \ap%lu%lu",ev1cnt,(ub8)ev1cnt,(ub8)hopcnt);

  info(CC0,"\ah%u hops before sample period",ltpatcnt);
  info(CC0,"\ah%u hops after sample period",gtpatcnt);

  ub4 nepatcnt = ltpatcnt + gtpatcnt;
  ub8 patperc = ((ub8)nepatcnt * 1000) / hopcnt;
  warncc(patperc > 10,0,"\ah%u of \ah%u hops outside sample period %lu%%%%",nepatcnt,hopcnt,patperc);
  if (globs.maxstops && patperc > 50) return 1;

  info(0,"%u of %u hops with constant duration, %u within accuracy",eqdur,hopcnt,accdur);
  info(CC0,"%u of %u ports colocated",colocnt,portcnt);
  info(CC0,"\ah%u of \ah%u dup hops in chain",eqhopcnt,hopcnt);

  ub8 sum = 0;
  ub4 iv,ccnt;
  ccnt = 0;
  for (iv = 0; iv <= cnthibin; iv++) {
    cnt = cntbins[iv];
    if (cnt) cnthvbin = iv;
  }
  for (iv = 0; iv <= cnthibin; iv++) {
    cnt = cntbins[iv];
    ccnt += cnt;
    sum += (ub8)cnt * (ub8)iv;
    if (ccnt == 0) continue;
    if (iv < 32 || iv >= cnthvbin - min(10,cnthvbin)) {
      info(0,"evs %u: \ah%u %lu%%",iv,ccnt,(sum * 100) / max(cumevcnt,1));
      ccnt = 0;
    } else if(!(iv % 10)) {
      msgopt("evhist"); info(0,"evs %u: \ah%u %lu%%",iv,ccnt,(sum * 100) / max(cumevcnt,1));
      ccnt = 0;
    }
  }

  ub4 at10,att0 = 0,att1 = hi32;
  ub4 agcd0,agcd1;
  ub8 agevcnt;

  for (aid = 0; aid < agencycnt; aid++) {
    hop = aghops[aid];
    if (hop == hi32) continue;
    error_ge(hop,hopcnt);
    hp = hops + hop;
    at10 = agtt1[aid] - agtt0[aid];
    agcd0 = day2cd(agtt0[aid] / 1440);
    agcd1 = day2cd(agtt1[aid] / 1440);
    msgopt("agency"); info(0,"agency %3u: %u - %u = %u day\as %s",aid,agcd0,agcd1,at10 / 1440,hp->iname);
    warncc(at10 < 8,Emp,"agency %u spans %u day\as: %u - %u %s",aid,at10,agcd0,agcd1,hp->iname);

    att0 = max(att0,agtt0[aid]);
    att1 = min(att1,agtt1[aid]);
    agcntp = agcntbins + aid * Agcntbins;
    ccnt = 0;
    sum = 0;
    agevcnt = 0;
    for (iv = 0; iv <= agcnthibin; iv++) {
      cnt = agcntp[iv];
      agevcnt += (ub8)cnt * (ub8)iv;
    }
    for (iv = 0; iv <= min(3,agcnthibin); iv++) {
      cnt = agcntp[iv];
      ccnt += cnt;
      sum += (ub8)cnt * (ub8)iv;
      info(CC0|Noiter,"%u evs-%u %lu%%",cnt,iv,(sum * 100) / agevcnt);
    }
  }
  basenet.tt0 = tt0;
  basenet.tt1 = tt1;

  info(Emp,"shared agency range \ad%u - \ad%u",att0,att1);

  for (aid = 0; aid < agencycnt; aid++) {
    hop = aghops[aid];
    if (hop == hi32) continue;
    error_ge(hop,hopcnt);
    hp = hops + hop;
    at10 = agtt1[aid] - agtt0[aid];
    agcd0 = day2cd(agtt0[aid] / 1440);
    agcd1 = day2cd(agtt1[aid] / 1440);

    agspnp = agspnbins + aid * ndt;
    sum = 0;
    for (iv = 0; iv < ndt; iv++) {
      sum += agspnp[iv];
    }
    ccnt = 0;
    for (iv = 0; iv < min(14,ndt); iv++) ccnt += agspnp[iv];
    if (ccnt == 0) continue;

    info(0,"agency %3u: %u - %u = %u day\as %s",aid,agcd0,agcd1,at10 / 1440,hp->iname);
    ccnt = 0;
    for (iv = 0; iv < min(14,ndt); iv++) {
      cnt = agspnp[iv];
      ccnt += cnt;
      info(CC0|Noiter,"%u span-%u %lu%%",cnt,iv,(100UL * ccnt) / sum);
    }
  }

  for (kind = 0; kind < Kindcntb; kind++) {
    hop = hihops[kind];
    if (hop != hi32) {
      hp = hops + hop;
      pdep = ports + hp->dep;
      parr = ports + hp->arr;
      info(0,"%s hop %u %s to %s hi speed %u %s",kindnames[kind],hop,pdep->iname,parr->name,hispeeds[kind],hp->name);
    }
    hop = lohops[kind];
    if (hop != hi32) {
      hp = hops + hop;
      pdep = ports + hp->dep;
      parr = ports + hp->arr;
      info(0,"%s hop %u %s to %s lo speed %u %s",kindnames[kind],hop,pdep->iname,parr->name,lospeeds[kind],hp->name);
    }
  }

  msgopt("pass1"); info0(0,"pass 1");

  // prepare hoplist in chain
  ub4 ci,idx,hichlen = 0,lochlen = hi32,hichain = 0,lochain = 0;
  ub4 cumchaincnt = 0,ridchainofs = 0;
  ub8 sum1,sum2;
  ub4 prvtdep;
  ub4 chstats[256];
  ub4 ivhi = Elemcnt(chstats) - 1;

  aclear(chstats);

  for (chain = 0; chain < rawchaincnt; chain++) {
    cp = chains + chain;
    cnt = cp->hopcnt;
    chstats[min(cnt,ivhi)]++;
    rid = cp->rid;
    if (rid == hi32) return error(0,"chain %u has no route",chain);
    rp = routes + rid;
    if (cnt == 0) {
      hop = cp->firsthop;
      info(Iter,"chain %u rtid %u rrid %u has no hops from %u %s",chain,cp->rtid,cp->rrid,hop,rp->name);
      continue;
    }
    ofs = cp->hopofs;
    if (cnt == 1) {
      chp = chainhops + ofs;
      hop = chp->hop;
      infocc(dbg,Notty,"rid %u chain %u has 1 hop %u %s",rid,chain,hop,rp->name);
    }
    if (cnt > hichlen) { hichlen = cnt; hichain = chain; }
    if (cnt < lochlen) { lochlen = cnt; lochain = chain; }
    infovrb(cnt > 200,0,"chain %u has %u hops",chain,cnt);
    rrid = cp->rrid;
    error_gt(rrid,hirrid,chain);
    rp->chaincnt++;
    cumchaincnt++;
    cp->rhopcnt = rp->hopcnt;
    error_z_cc(cp->rhopcnt,"cnt %u rid %u",cnt,rid);

    hidur = cp->hitarr - cp->lotdep;
    infocc(hidur > 720,Notty|Iter,"chain %u rrid %u hidur %u",chain,rrid,hidur);
    if (hidur > 720) {
      hp1 = hops + cp->lotdhop;
      hp2 = hops + cp->hitahop;
      dep = hp1->dep; arr = hp1->arr;
      pdep = ports + dep; parr = ports + arr;
      info(Notty|Iter," dep hop %u td \ad%u %s %s to %s",cp->lotdhop,cp->lotdep,hp1->name,pdep->name,parr->name);
      dep = hp2->dep; arr = hp2->arr;
      pdep = ports + dep; parr = ports + arr;
      info(Notty|Iter," arr hop %u ta \ad%u %s %s to %s",cp->hitahop,cp->hitarr,hp2->name,pdep->name,parr->name);
    }
    chip = chainidxs + ofs;
    sort8(chip,cnt,FLN,"chainhops");

    sum1 = sum2 = 0;
    dist = 0; midur = prvdur = prvtdep = 0;
    for (ci = 0; ci < cnt; ci++) {
      tripseq = (ub4)(chip[ci] >> 32);
      error_z(tripseq,chain);
      idx = chip[ci] & hi32;
      error_ge(idx,cnt);
      error_ovf(idx,ub2);
      chp = chainhops + ofs + idx;
      chp->seq = tripseq;
      hop = chp->hop;
      error_ge(hop,hopcnt);
      hp = hops + hop;
      error_ne(hp->rid,rid);
      rhop = hp->rhop;
      error_ge(rhop,rp->hopcnt);
      tdep = chp->tdep;
      if (chain == tid2watch) {
        info(0,"rid %u tid %u r.hop %u.%u at %u td %u ta %u seq %u",rid,chain,hp->rhop,hop,ci,tdep,chp->tarr,tripseq);
      }
      if (tdep < prvtdep) {
        pdep = ports + hp->dep;
        parr = ports + hp->arr;
        warn(0,"hop %u tdep %u before arr %u %s %s to %s",hop,tdep,prvtdep,hp->name,pdep->name,parr->name);
        cp->hopcnt = cnt;
        break;
//        error_lt(tdep,prvtdep);
      }
      prvtdep = tdep;
      dist += hp->dist;
      if (hp->tp.midur == hi32) { prvdur = midur; midur = hi32; }
      else midur += hp->tp.midur;
      chp->midur = midur;
      if (midur == hi32) midur = prvdur;
      sum1 = (sum1 + hop) % hi32;
      sum2 = (sum2 + sum1) % hi32;
    }
    sum = (sum2 << 32) | sum1;
    cp->code = sum;
  }

  for (iv = 0; iv <= ivhi; iv++) infocc(chstats[iv],Notty,"%u chain\as of length %u",chstats[iv],iv);

  // list shortest and longest chain
  lochlen = min(lochlen,hichlen);

  cp = chains + hichain;

  rid = cp->rid; rrid = cp->rrid;
  rp = routes + rid;
  info(0,"\ah%u chains len %u .. %u",cumchaincnt,lochlen,hichlen);
  info(0,"longest chain %u len %u rid %u rrid %u %s",hichain,hichlen,rid,rrid,rp->name);
  cnt = cp->hopcnt;
  chp = chainhops + cp->hopofs;
  chip = chainidxs + cp->hopofs;
  for (ci = 0; ci < cnt; ci++) {
    idx = chip[ci] & hi32;
    tripseq = (ub4)(chip[ci] >> 32);
    hop = chp[idx].hop;
    tdep = chp[idx].tdep;
    hp = hops + hop;
    pdep = ports + hp->dep;
    parr = ports + hp->arr;
    info(Notty|V0,"  hop %u %u-%u at \ad%u %s to %s seq %u",hop,hp->dep,hp->arr,tdep,ci == 0 ? pdep->iname : pdep->name,parr->name,tripseq);
  }

  cnt = 0;
  for (hop = 0; hop < hopcnt; hop++) {
    hp = hops + hop;
    if (hp->rrid != rrid) continue;
    pdep = ports + hp->dep;
    parr = ports + hp->arr;
    vrb(0,"  hop %u %u-%u %s to %s",hop,hp->dep,hp->arr,pdep->name,parr->name);
    cnt++;
  }
  info(0,"%u hop\as on rid %u rrid %u",cnt,rid,rrid);

  cp = chains + lochain;
  info(0,"shortest chain %u len %u rid %u rrid %u",lochain,lochlen,cp->rid,cp->rrid);
  cnt = cp->hopcnt;
  ofs = cp->hopofs;
  chp = chainhops + ofs;
  chip = chainidxs + ofs;
  for (ci = 0; ci < cnt; ci++) {
    idx = chip[ci] & hi32;
    tripseq = (ub4)(chip[ci] >> 32);
    hop = chp[idx].hop;
    hp = hops + hop;
    pdep = ports + hp->dep;
    parr = ports + hp->arr;
    info(0,"  hop %u %u-%u seq %u %s to %s",hop,hp->dep,hp->arr,tripseq,pdep->name,parr->name);
  }

  // list chains per route
  ub4 *routechains = alloc(cumchaincnt,ub4,0,"chain routechains",cumchaincnt);

  for (rid = 0; rid < ridcnt; rid++) {
    rp = routes + rid;
    cnt = rp->chaincnt;
    vrb(0,"rid %u rrid %u has %u chains",rid,rp->rrid,cnt);
    rp->chainofs = ridchainofs;
    ridchainofs += cnt;
  }
  error_ne(ridchainofs,cumchaincnt);

  ub4 chainpos,hi2chainlen = 0,hirid = 0,hidtid = 0,hidtrid = 0;
  for (chain = 0; chain < rawchaincnt; chain++) {
    cp = chains + chain;
    cnt = cp->hopcnt;
    if (cnt == 0) continue;
    rid = cp->rid;
    error_eq(rid,hi32);
    rp = routes + cp->rid;
    chainpos = rp->chainpos;
    if (chainpos == 0) rp->lochain = chain;
    error_ge(rp->chainofs + chainpos,cumchaincnt);
    routechains[rp->chainofs + chainpos] = chain;
    rp->hichainlen = max(rp->hichainlen,cnt);
    if (rp->hichainlen > hi2chainlen) { hi2chainlen = rp->hichainlen; hirid = cp->rid; }
    cp->dtid = chainpos;
    if (chainpos == Bdtidlim) warn(0,"rid %u dtid at limit %u",rid,chainpos);
    if (chainpos > hidtid) { hidtid = chainpos; hidtrid = rid; }
    rp->chainpos = chainpos + 1;
    // infocc(rid == 50,0,"chain %u pos %u",chain,chainpos);
    error_ge(chainpos,hi16);
  }
  info(Emp,"hi dtid %u for route %u",hidtid,hidtrid);
  info(Emp,"longest chain %u for route %u",hi2chainlen,hirid);

  for (rid = 0; rid < ridcnt; rid++) {
    rp = routes + rid;
    rrid = rp->rrid;
    cnt = rp->hichainlen;
    vrb(0,"r.rid %u.%u hilen %u cnt %u",rrid,rid,cnt,rp->hopcnt);
  }

  basenet.hichainlen = hichlen;

  basenet.routechains = routechains;
  basenet.chainhops = chainhops;
  basenet.chainidxs = chainidxs;

  eventmem = &basenet.eventmem;
  ub8 *ev = basenet.events = mkblock(eventmem,cumevcnt,ub8,Noinit,"time base-events");

  ub4 evofs = 0,maplen;
  for (hop = 0; hop < hopcnt; hop++) {
    hp = hops + hop;
    tp = &hp->tp;
    evcnt = hp->evcnt;
    tp->evofs = evofs;
    evofs += 2 * evcnt;
  }
  error_ne(evofs,cumevcnt * 2);

  for (sid = 0; sid < sidcnt; sid++) {
    sp = sids + sid;
    if (sp->valid == 0) continue;
    lolt0day = min(lolt0day,sp->lt0day);
    hilt1day = max(hilt1day,sp->lt1day);
  }

  dstmaplen = hilt1day + 1 - lolt0day;

  dstmap = talloc0(dstmaplen,ub1,0);

  // pass 2: fill from time entries
  msgopt("pass2a"); info(0,"preparing \ah%lu events in %u base hops pass 2",cumevcnt,hopcnt);

  ub4 prvt,ei,rt;
  ub4 overtakecnt = 0,overtakehi = 0;
  ub8 cumevcnt2 = 0;
  ub4 noevcnt2 = 0;
  ub4 dtid;

  for (hop = 0; hop < hopcnt; hop++) {

    msgprefix(0,NULL);
    if (progress(&eta,"hop %u of %u in pass 2, \ah%lu events",hop,hopcnt,cumevcnt2)) return 1;

    hp = hops + hop;

    dep = hp->dep;
    arr = hp->arr;
    pdep = ports + dep;
    parr = ports + arr;

    aid = rp->aid;
    agp = agencies + aid;
    agtime = agp->tznlen;

    rid = hp->rid;
    error_ge(rid,ridcnt);
    rp = routes + rid;

    msgprefix(0,"rid %u hop %u",rid,hop);

    if (hp->t1 <= hp->t0) return error(0,"no range \ad%u .. \ad%u",hp->t0,hp->t1);

    timespos = hp->timespos;
    timecnt = hp->timecnt;
    tbp = timesbase + timespos * Tentries;
    evcnt = 0;
    hdt = hp->t1 - gt0 + daymin;
    error_ge(hdt,xtimelen);
    tp = &hp->tp;

    lochain = rp->lochain;
    chainpos = rp->chainpos;

      if (agtime) {
        utcofsd = utcofsa = agp->utcofs;
        dstonofd = dstonofa = agp->dstonof;
      } else {
        utcofsd = pdep->utcofs;
        utcofsa = parr->utcofs;
        dstonofd = pdep->dstonof;
        dstonofa = parr->dstonof;
      }

    error_ne(tp->hop,hop);

    lolt0day = hp->lt0day;
    hilt1day = hp->lt1day;

    dstmaplen = hilt1day - lolt0day + (bDurlim / 1440) + 2;

    for (day = lolt0day; day <= hilt1day; day++) dstmap[day - lolt0day] = indst(day,dstonof);

    vndx = 0;
    for (tndx = 0; tndx < timecnt; tndx++) {
      sid = tbp[Tesid];
      if (sid >= sidcnt) { tbp += Tentries; continue; }  // skip non-contributing entries disabled above

      vndx++;
      tid = tbp[Tetid];
      tripno = tbp[Tetripno];

      tdepsec = tbp[Tetdep];
      tarrsec = tbp[Tetarr];
      trepivsec = tbp[Terepiv];
      trepstartsec = tbp[Terepstart];
      trependsec = tbp[Terepend];

      tripseq = tbp[Teseq];
      srdep = tbp[Tesdep];
      srarr = tbp[Tesarr];

      tdep = (tdepsec + 30) / 60;
      tarr = (tarrsec + 30)/ 60;
      trepiv = (trepivsec + 30) / 60;
      trepstart = (trepstartsec + 30) / 60;
      trepend = (trependsec + 30) / 60;

      if (utcofsa < utcofsd) {
        tarrd = tarr + (utcofsd - utcofsa);
      } else {
        error_lt(tarr,utcofsa - utcofsd);
        tarrd = tarr - (utcofsa - utcofsd);
      }

      error_lt(tarrd,tdep);
      dur = tarrd - tdep;

      error_lt(tid,lochain);
      dtid = tid - lochain;
      error_ge(dtid,Bdtidlim);
      error_ge_cc(dtid,chainpos,"tid %u",tid);
      error_ge_cc(dtid,rp->chaincnt,"tid %u",tid);

      infocc(rid == 0 && dtid > 1800,0,"dtid %u cnt %u",dtid,rp->chaincnt);

      rtid = tid2rtid[tid];

//      infocc(trepiv > 1,0,"trep %u tdep %u end %u",trepiv,tdep,trepend);

      warncc(tarr < tdep,0,"tdep %u tarr %u at index %u",tdepsec,tarrsec,tndx);
      error_ge(dur,hi16);
      sp = sids + sid;

      // infocc(hop == 7649 || hop == 7650,0,"tid %u seq %u td \ad%u ta \ad%u",tid,tripseq,tdep,tarr);

      lt0day = sp->lt0day;

      mapofs = sp->mapofs;
      daymap = sidmaps + mapofs;
      maplen = sp->maplen;

      mapday = lolt0day - lt0day;
      error_ge(mapday,maplen);

      mapday = hilt1day - lt0day;
      error_ge(mapday,maplen);

      for (day = lolt0day; day <= hilt1day; day++) {

        lt0day = sp->lt0day;
        if (day < lt0day) continue;
        if (day > sp->lt1day) continue;

        if (daymap[mapday] == 0) continue;

        t0 = sp->t0;
        t1 = sp->t1;

        dday = day + tdep / 1440;
        error_ge(dday,dstmaplen);

        todo freqevs

        lt = day * daymin + tdep;
        tt = lmin2mini(lt,utcofs);
        if (dstmap[dday]) tt -= 60;
        rt = tt - gt0;
        tmpevs[cnt] = ((ub8)rt << Btimshift) | ((ub8)srda << Bsrdashift) | ((ub8)dtid << Bdtidshift) | (ub8)dur;
        cnt++;
       } // each day
     } // each entry
     error_z(cnt,hop);

     // sort and remove duplicates
     fsort8(tmpevs,cnt,0,FLN,"base evs");
     cnt2 = 0;
     evp = events + evofs + evcnt;
     for (ei = 0; ei < cnt; ei++) {
       x = tmpevs[ei];
       rt = x >> Btimshift;
       if (ei && rt == prvrt) { dup++; continue; }
       evp[cnt2] = x;
       prvrt = rt;
     }
     evcnt += cnt2;

#if 0
      tdeprep = tdep | (trepiv << 16);
      cnt = fillxtime2(tp,xp,xpacc,xtimelen,gt0,sp,daymap,maplen,tdeprep,trepstart,trepend,dtid,dur,srdep,srarr,evcnt);
      hoplog(hop,0,"r.tid %u.%u rsid %x \ad%u \ad%u td \ad%u ta \ad%u %u events seq %u",rtid,tid,sp->rsid,t0,t1,tdep,tarr,cnt,tripseq);

#endif

      if (evcnt > maxev4hop) {
        warning(0,"hop %u exceeds event max %u %s",hop,maxev4hop,hp->name);
        hp->timecnt = tndx;
        break;
      }
      tbp += Tentries;
    } // each time entry
    if (timecnt == 0) continue;
    error_z(evcnt,0);

    if (period0 > tp->t0 + gt0 || period1 < tp->t1 + gt0) {
      cnt = filterxtime(tp,xp,xpacc,xtimelen,period0,period1);
      error_gt(cnt,evcnt,0);
      evcnt = cnt;
    }
    error_z(evcnt,0);

    error_gt(evcnt,tp->evcnt,timecnt);
    error_ge(tp->evcnt - evcnt,10);
    if (evcnt == 0 && vndx) {
      info(0,"no events for %u time entries",timecnt);
      continue;
    }

    cnt = filltrep(&basenet,chains,rawchaincnt,rid,eventmem,tp,xp,xpacc,xtimelen);
    hoplog(hop,0,"evtcnt %u and %u",cnt,hp->evcnt);
    error_ne(cnt,evcnt);

    if (cnt != hp->evcnt) {
      return error(0,"hop %u evcnt %u != hp->evcnt %u",hop,evcnt,hp->evcnt);
    }
    if (cnt == 0) noevcnt++;

    // check
    if (do_chkev) {
      ev = basenet.events + tp->evofs;
      if (evcnt) {
        prvt = (ub4)ev[0];
        for (ei = 1; ei < evcnt; ei++) {
          rt = (ub4)ev[ei * 2];
          dur = (ub4)(ev[ei * 2] >> 32);
          tid = (ub4)ev[ei * 2 + 1] & hi24;
          infocc(rt <= prvt,0,"cnt %u  ",evcnt);
          error_le(rt,prvt);
          error_eq(rt,hi32);
        // infocc(hop == 7642 || hop == 7644,0,"ev %u tid %u td \ad%u dur %u",ei,tid,rt + gt0,dur);
        }
      } else {
        info0(0,"no evs");
      }
    }

    clearxtime(tp,xp,xpacc,xtimelen);

    if (cumevcnt2 + evcnt > maxzev) {
      warning(0,"hop %u: exceeding total event max \ah%lu %s",hop,maxzev,hp->name);
      break;
    }

    vrb(0,"hop %u \ah%u time events %s",hop,evcnt,hp->name);
    cumevcnt2 += evcnt;
    if (tp->overtake) {
      overtakecnt++;
      overtakehi = max(overtakehi,tp->overtakehi);
    }
  } // each hop

  afree0(xpacc);
  afree0(xp);

  msgprefix(0,NULL);
  info(0,"\ah%lu time events, avg %u per hop",cumevcnt,(ub4)(cumevcnt / hopcnt));
  info(CC0,"%u,%u hops without events",noevcnt2,noevcnt);
  error_ne(noevcnt,noevcnt2);
  error_gt(cumevcnt2,cumevcnt,0);

  info(CC0,"\ah%u hops with overtaking events, max %u min",overtakecnt,overtakehi);

  memrdonly(basenet.events,cumevcnt * 2 * sizeof(ub8));

  afree(sidmaps,"time sidmap");
  basenet.sidmaps = NULL;

  // free timesbase
  trimblock(&basenet.timesmem,0,ub4);

  msgopt("pass2"); info(0,"done preparing %u base hops",hopcnt);

  return 0;
}

int prepbasenet(void)
{
  int rv = prepbase();
  nomsgpfx();
  return rv;
}

void ininetbase(void)
{
  msgfile = setmsgfile(__FILE__);
  iniassert();
}
