// net.c - main network setup

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2016 Joris van der Geer.
 */

/* Initialize the network once at startup :

   create a pre-computed connectivity network used in search

   - infer walk and taxi links

   - assess global connectivity

   - Build connectivity matrix between any 2 full ports
     base matrix for direct (non-stop) hops
     derived matrix for each of n intermediate hops

     each matrix contains a top-N list of possible trips from port A to port B
     the list is trimmed on distance heuristics
 */

#include <stdarg.h>
#include <string.h>

#include "base.h"
#include "cfg.h"
#include "mem.h"
#include "math.h"

static ub4 msgfile;
#include "msg.h"

#include "iadr.h"
#include "util.h"
#include "time.h"
#include "net.h"
#include "fare.h"

#include "net1.h"
#include "net2.h"
#include "net3.h"
#include "netev.h"
#include "osm.h"

#undef hdrstop

static ub4 nowalklines = 0; // suppress walk links besides service links
static int useprofile = 1;  // use profile-based taxi link assessment

static struct network gs_net;

static ub4 msgrep[8192];
#define Msgrep (msgrep[min(__LINE__,8191)]++ < 100)

void ininet(void)
{
  msgfile = setmsgfile(__FILE__);
  iniassert();
}

struct network *getnet(void)
{
  return &gs_net;
}

// mark local links on base hops
static int marklocal(struct network *net)
{
  ub4 ndep,narr;
  struct chop *hp,*chops = net->chops;
  struct port *pdep,*parr,*ports = net->ports;
  ub4 *portsbyhop = net->portsbyhop;
  ub4 hop,dep,arr;
  ub4 rid;
  ub4 hopcnt = net->hopcnt;
  ub4 portcnt = net->portcnt;

  for (hop = 0; hop < hopcnt; hop++) {

    dep = portsbyhop[hop * 2];
    arr = portsbyhop[hop * 2 + 1];
    if (dep == arr) continue;
    if (dep == hi32 || arr == hi32) continue;

    error_ge(dep,portcnt);
    error_ge(arr,portcnt);

    hp = chops + hop;
    if (hp->evcnt == 0) continue;

    pdep = ports + dep;
    parr = ports + arr;

    ndep = pdep->ndep;
    narr = parr->narr;

    pdep->ndep = ndep+1;
    parr->narr = narr+1;

    rid = hp->rid;

    if (ndep < Nlocal) {
      pdep->deps[ndep] = arr; pdep->drids[ndep] = rid;
    }
    if (narr < Nlocal) {
      parr->arrs[narr] = dep; parr->arids[narr] = rid;
    }

  }
  return 0;
}

// mark links on walk hops
static int markwhops(struct network *net)
{
  ub4 ndep,narr;
  struct chop *hp,*chops = net->chops;
  struct port *pdep,*parr,*ports = net->ports;
  ub4 *portsbyhop = net->portsbyhop;
  ub4 hop,dep,arr;
  ub4 thopcnt = net->thopcnt;
  ub4 whopcnt = net->whopcnt;
  ub4 portcnt = net->portcnt;

  for (hop = thopcnt; hop < whopcnt; hop++) {
    dep = portsbyhop[hop * 2];
    arr = portsbyhop[hop * 2 + 1];
    if (dep == arr) continue;
    if (dep == hi32 || arr == hi32) continue;

    error_ge(dep,portcnt);
    error_ge(arr,portcnt);

    hp = chops + hop;

    pdep = ports + dep;
    parr = ports + arr;

    ndep = pdep->ndep;
    narr = parr->narr;

    pdep->ndep = ndep+1;
    parr->narr = narr+1;
  }
  return 0;
}

// check distance for lat range.
static ub4 chkdista(struct port *pdep,struct port *parr,double dstlim)
{
  double dist;

  if (pdep->lat == parr->lat && pdep->lon == parr->lon) return 0;
  dist = geodist(pdep->rlat,pdep->rlon,parr->rlat,parr->rlon,pdep->name);
  if (dist < dstlim) return (ub4)dist;
  dist = geodist(pdep->rlat,pdep->rlon,parr->rlat,pdep->rlon,pdep->name);
  if (dist < dstlim * 1.5) return hi32-1;
  else return hi32;
}

// idem for lon range
static int chkdisto(struct port *pdep,struct port *parr,double dstlim)
{
  double dist;

  if (pdep->lat == parr->lat && pdep->lon == parr->lon) return 0;
  dist = geodist(pdep->rlat,pdep->rlon,parr->rlat,parr->rlon,pdep->name);
  if (dist < dstlim) return (ub4)dist;
  dist = geodist(pdep->rlat,pdep->rlon,pdep->rlat,parr->rlon,pdep->name);
  if (dist < dstlim * 1.5) return hi32-1;
  else return hi32;
}

// get distance based on road map
static ub4 mapdist(void *vosm,ub4 fln,ub4 depnid,ub4 arrnid,enum osmodes mode,ub4 distlim,struct port *pdep,struct port *parr,ub4 *ptime)
{
  struct osmres res;
static int cnt;
  int show = 0;
  ub4 dist,xdist,cdist;
  double fdist;

  if (ptime) *ptime = 0;
  error_zp(vosm,0);
  if (depnid == hi32 || arrnid == hi32) return hi32;

  fdist = geodist(pdep->rlat,pdep->rlon,parr->rlat,parr->rlon,"map");
  cdist = (ub4)(fdist + 0.5);
  xdist = pdep->nidist + parr->nidist;

  if (cnt++ < 2) show = 1;
  if (depnid == arrnid) {
    dist = cdist;
    if (ptime) *ptime = cdist / 100;
    return cdist;
  }
  if (osmplan(vosm,depnid,arrnid,distlim * 2,mode,show,&res)) return hi32;

  if (res.dist == hi32) {
    if (osmplan(vosm,arrnid,depnid,distlim * 2,mode,show,&res)) return hi32;
  }
  if (res.dist == hi32) {
    dist = cdist;
    if (ptime) *ptime = cdist / 100;
    return cdist;
  }

  if (ptime) *ptime = res.time + xdist / 100;
  dist = res.dist + xdist;
  infocc(dist == 0,0,"dist 0 for \ar%f,\ar%f \ar%f,\ar%f %s to %s",pdep->rlat,pdep->rlon,parr->rlat,parr->rlon,pdep->name,parr->name);

  if (cdist > dist + 20) {
    if (Msgrep) warnfln(fln,0,"dist %u dir %u for \ar%f,\ar%f \ar%f,\ar%f %s to %s",dist,cdist,pdep->rlat,pdep->rlon,parr->rlat,parr->rlon,pdep->iname,parr->iname);
    cdist = dist;
  }
  return dist;
}

static inline ub4 walkdur(ub4 dist,ub4 speed)
{
  return min(1 + (dist * 60) / speed,Durlim);
}

// infer walk links
static int mkwalk(struct network *net)
{
  ub4 portcnt = net->portcnt;
  ub4 hopcnt = net->hopcnt;
  ub4 chopcnt = net->chopcnt;
  ub4 thopcnt = net->thopcnt;
  struct port *ports,*pdep,*parr;
  struct chop *hp,*hops = net->chops;
  char *dname;
  ub4 dist,lodist = hi32,hidist = 0;
  ub4 dep,arr;
  ub8 port2;
  ub4 walklimit = net->walklimit;  // geo's
  ub4 walkspeed = net->walkspeed;  // geo's per hour
  ub4 walklim2 = walklimit / 2;
  void *vosm = net->vosm;

  struct eta eta;

  if (portcnt == 0) return error(0,"no ports for %u hops net",hopcnt);
  if (hopcnt == 0) return error(0,"no hops for %u port net",portcnt);

  net->whopcnt = thopcnt;

  if (globs.nowalk) return info0(0,"walk links disabled in cfg");
  if (walklimit < 2) return info(0,"no walk links for %u m limit",walklimit * 10);

  port2 = (ub8)portcnt * portcnt;

  ports = net->ports;

  double wlim_geo = (double)walklimit * 1.2;

  ub4 hop,whop,whopcnt = 0;
  ub4 minicnt = 0;

  // create rudimentary net0 without walk links
  iadrbase net0;
  oclear(net0);
  if (mkiadr0(&net0,portcnt,portcnt,ub2,20000,16,"net0")) return 1;

  if (nowalklines) {
    info0(0,"create mini net0");
    if (mkiadrmap(&net0,"net0 cntmap")) return 1;

    for (hop = 0; hop < chopcnt; hop++) {
      hp = hops + hop;
      if (hp->kind == Taxi) continue;
      if (hp->evcnt < 100) continue; // todo
      iadrinc(&net0,hp->dep,hp->arr,0);
      minicnt++;
    }
    info(0,"created \ah%u item mini net0",minicnt);
  }

  ub4 *latsort = net->latsort;
  ub4 *lonsort = net->lonsort;
  ub4 *latsortidx = net->latsortidx;
  ub4 *lonsortidx = net->lonsortidx;

  // init
  ub4 *as = talloc(portcnt,ub4,0,"net0 walks",portcnt);
  ub4 *os = talloc(portcnt,ub4,0,"net0 walks",portcnt);

  ub4 *walkmap = talloc(portcnt,ub4,0,"net0 walks",portcnt);

  ub4 a,o,al,ar,ol,or,ni;
  ub4 dlat,dlon;

  for (dep = 0; dep < portcnt; dep++) {
    if (progress(&eta,"pass 0 port %u of %u for \ah%lu distance pairs",dep,portcnt,port2)) return 1;
    pdep = ports + dep;
    if (pdep->valid == 0) continue;
    dname = pdep->name;
    dlat = pdep->lat; dlon = pdep->lon;

    a = bsearch4(latsort,portcnt,dlat,FLN,dname);
    o = bsearch4(lonsort,portcnt,dlon,FLN,dname);
    error_ge(a,portcnt);
    error_ge(o,portcnt);
    as[dep] = a;
    os[dep] = o;
  }

  ub4 hiport = 0,hicnt = 0;
  ub4 nda,shortlim,longlim,wscnt,wlcnt,wscnt1,wlcnt1;

  ub4 *mapuse = talloc0(portcnt,ub4,0);
  ub4 use,usecnt;

  // count pass
  for (dep = 0; dep < portcnt; dep++) {
    if (progress(&eta,"pass 1 walks port %u of %u for \ah%lu distance pairs",dep,portcnt,port2)) return 1;
    pdep = ports + dep;
    if (pdep->valid == 0) continue;

    dname = pdep->name;

    usecnt = 1;
    mapuse[0] = dep;
    walkmap[dep] = 1;

    a = as[dep];
    o = os[dep];

    ar = a;
    or = o;
    al = a + 1;
    ol = o + 1;

    wlcnt = wscnt = 0;
    nda = pdep->nda;

    // todo in config
    if (nda < 5) { longlim = 120; shortlim = 160;
    } else if (nda < 13) { longlim = 160; shortlim = 280;
    } else { longlim = 200; shortlim = 400; }

    while (ar < portcnt) {
      ni = latsortidx[ar++];
      if (walkmap[ni]) continue;
      parr = ports + ni;
      dist = chkdista(pdep,parr,wlim_geo);
      if (dist == hi32) break;
      else if (dist == hi32 - 1) continue;
      if (nowalklines && iadrinmap(&net0,dep,ni)) continue;
      walkmap[ni] = 1;
      mapuse[usecnt++] = ni;
      if (dist < walklim2) wscnt++;
      else wlcnt++;
    }

    while (al) {
      ni = latsortidx[--al];
      if (walkmap[ni]) continue;
      parr = ports + ni;
      dist = chkdista(pdep,parr,wlim_geo);
      if (dist == hi32) break;
      else if (dist == hi32 - 1) continue;
      if (nowalklines && iadrinmap(&net0,dep,ni)) continue;
      walkmap[ni] = 1;
      mapuse[usecnt++] = ni;
      if (dist < walklim2) wscnt++;
      else wlcnt++;
    }

    while (or < portcnt) {
      ni = lonsortidx[or++];
      if (walkmap[ni]) continue;
      parr = ports + ni;
      dist = chkdisto(pdep,parr,wlim_geo);
      if (dist == hi32) break;
      else if (dist == hi32 - 1) continue;
      if (nowalklines && iadrinmap(&net0,dep,ni)) continue;
      walkmap[ni] = 1;
      mapuse[usecnt++] = ni;
      if (dist < walklim2) wscnt++;
      else wlcnt++;
    }

    while (ol) {
      ni = lonsortidx[--ol];
      if (walkmap[ni]) continue;
      parr = ports + ni;
      dist = chkdisto(pdep,parr,wlim_geo);
      if (dist == hi32) break;
      else if (dist == hi32 - 1) continue;
      if (nowalklines && iadrinmap(&net0,dep,ni)) continue;
      walkmap[ni] = 1;
      mapuse[usecnt++] = ni;
      if (dist < walklim2) wscnt++;
      else wlcnt++;
    }
    pdep->nwsdep = wscnt;
    pdep->nwldep = wlcnt;
    whopcnt += min(wscnt,shortlim);
    whopcnt += min(wlcnt,longlim);
    if (wscnt + wlcnt > hicnt) { hicnt = wscnt + wlcnt; hiport = dep; }

    for (use = 0; use < usecnt; use++) {
      ni = mapuse[use];
      walkmap[ni] = 0;
    }

  }

  info(Emp,"\ah%u tentative inferred walk links below \ag%u (%u), range %u-%u",whopcnt,walklimit,walklimit,lodist,hidist);

  pdep = ports + hiport;
  info(0,"port %u with %u con has %u short and %u long walk links %s",dep,pdep->nda,pdep->nwsdep,pdep->nwldep,pdep->iname);

  ub4 *orgportsbyhop = net->portsbyhop;
  ub4 *orghopdist = net->hopdist;
  struct chop *orgchops = net->chops;

  ub4 newhopcnt = thopcnt + whopcnt;

  ub4 *portsbyhop = alloc(newhopcnt * 2,ub4,0,"net portsbyhop",newhopcnt);
  memcpy(portsbyhop,orgportsbyhop,thopcnt * 2 * sizeof(ub4));

  ub4 *hopdist = alloc(newhopcnt,ub4,0,"net hopdist",newhopcnt);
  memcpy(hopdist,orghopdist,thopcnt * sizeof(ub4));

  struct chop *chp,*newchops = alloc(newhopcnt,struct chop,0,"net chop",0);
  memcpy(newchops,orgchops,thopcnt * sizeof(struct chop));

  ub4 hiwhop = hi32,lowhop = hi32;
  ub4 nowalk = 0;
  whop = thopcnt;

  ub4 nid;

  for (dep = 0; vosm && dep < portcnt; dep++) {
    if (progress(&eta,"pass 1b port %u of %u for \ah%lu distance pairs",dep,portcnt,port2)) return 1;
    pdep = ports + dep;
    if (pdep->valid == 0) continue;
    if (pdep->nwsdep == 0 && pdep->nwldep == 0) continue;
    nid = lookupnid(vosm,pdep->lat * 10,pdep->lon * 10,Osfoot,&dist);
    infocc(dist > 10 * 100,0,"port %u dist \ag%u %s",dep,dist,pdep->iname);
    if (dist > walklimit * 100) {
      info(0,"port %u off-map dist \ag%u %s",dep,dist,pdep->iname);
      nid = hi32;
    } else pdep->nidist = dist;
    pdep->nidfoot = nid;
  }

  // fill pass
  for (dep = 0; dep < portcnt; dep++) {
    pdep = ports + dep;
    if (progress(&eta,"pass 2 walks port %u of %u for \ah%lu pairs %s",dep,portcnt,port2,pdep->iname)) return 1;
    if (pdep->valid == 0) continue;

    dname = pdep->name;

    usecnt = 1;
    mapuse[0] = dep;
    walkmap[dep] = 1;

    a = as[dep];
    o = os[dep];

    ar = a;
    or = o;
    al = a + 1;
    ol = o + 1;

    nda = pdep->nda;
    nid = pdep->nidfoot;

    // todo in config
    if (nda < 5) { longlim = 120; shortlim = 160;
    } else if (nda < 13) { longlim = 160; shortlim = 280;
    } else { longlim = 200; shortlim = 400; }

    wscnt1 = pdep->nwsdep;
    wlcnt1 = pdep->nwldep;
    wscnt = wlcnt = 0;

    while (ar < portcnt && wscnt < shortlim && wlcnt < longlim && whop < newhopcnt) {
      ni = latsortidx[ar++];
      if (walkmap[ni]) continue;
      parr = ports + ni;
      dist = chkdista(pdep,parr,wlim_geo);
      if (dist == hi32) break;
      else if (dist == hi32 - 1) continue;
      if (nowalklines && iadrinmap(&net0,dep,ni)) continue;
      if (vosm && nid != hi32 && parr->nidfoot != hi32) dist = mapdist(vosm,FLN,nid,parr->nidfoot,Osfoot,walklimit,pdep,parr,NULL);
      if (dist == hi32) nowalk++;
      if (dist > walklimit) continue;

      infocc(Msgrep,0,"%u-%u %u-%u dist \ag%u \ar%f,\ar%f \ar%f,\ar%f %s to %s",
        dep,ni,nid,parr->nidfoot,dist,pdep->rlat,pdep->rlon,parr->rlat,parr->rlon,pdep->iname,parr->iname);
      if (vosm && dist == 0) {
        warn(0,"dist 0 for %u-%u \ar%f,\ar%f \ar%f,\ar%f",dep,ni,pdep->rlat,pdep->rlon,parr->rlat,parr->rlon);
        continue;
      }
      if (dist < walklim2) {
        if (wscnt1 > shortlim && rnd(wscnt1) > shortlim) continue;
        wscnt++;
      } else {
        if (wlcnt1 > longlim && rnd(wlcnt1) > longlim) continue;
        wlcnt++;
      }
      chp = newchops + whop;
      error_ge(whop - thopcnt,newhopcnt - thopcnt);
      walkmap[ni] = 1;
      mapuse[usecnt++] = ni;
      portsbyhop[whop * 2] = dep;
      portsbyhop[whop * 2 + 1] = ni;
      chp->lodur = walkdur(dist,walkspeed);
      chp->dist = dist;
      whop++;
    }

    while (al && wscnt < shortlim && wlcnt < longlim && whop < newhopcnt) {
      ni = latsortidx[--al];
      if (walkmap[ni]) continue;
      parr = ports + ni;
      dist = chkdista(pdep,parr,wlim_geo);
      if (dist == hi32) break;
      else if (dist == hi32 - 1) continue;
      if (nowalklines && iadrinmap(&net0,dep,ni)) continue;
      if (vosm && nid != hi32 && parr->nidfoot != hi32) dist = mapdist(vosm,FLN,nid,parr->nidfoot,Osfoot,walklimit,pdep,parr,NULL);
      if (dist == hi32) nowalk++;
      if (dist > walklimit) continue;

      if (dist < walklim2) {
        if (wscnt1 > shortlim && rnd(wscnt1) > shortlim) continue;
        wscnt++;
      } else {
        if (wlcnt1 > longlim && rnd(wlcnt1) > longlim) continue;
        wlcnt++;
      }
      chp = newchops + whop;
      error_ge(whop,newhopcnt);
      walkmap[ni] = 1;
      mapuse[usecnt++] = ni;
      portsbyhop[whop * 2] = dep;
      portsbyhop[whop * 2 + 1] = ni;
      chp->lodur = walkdur(dist,walkspeed);
      chp->dist = dist;
      whop++;
    }

    while (or < portcnt && wscnt < shortlim && wlcnt < longlim && whop < newhopcnt) {
      ni = lonsortidx[or++];
      if (walkmap[ni]) continue;
      parr = ports + ni;
      dist = chkdisto(pdep,parr,wlim_geo);
      if (dist == hi32) break;
      else if (dist == hi32 - 1) continue;
      if (nowalklines && iadrinmap(&net0,dep,ni)) continue;
      if (vosm && nid != hi32 && parr->nidfoot != hi32) dist = mapdist(vosm,FLN,nid,parr->nidfoot,Osfoot,walklimit,pdep,parr,NULL);
      if (dist == hi32) nowalk++;
      if (dist > walklimit) continue;

      if (dist < walklim2) {
        if (wscnt1 > shortlim && rnd(wscnt1) > shortlim) continue;
        wscnt++;
      } else {
        if (wlcnt1 > longlim && rnd(wlcnt1) > longlim) continue;
        wlcnt++;
      }
      chp = newchops + whop;
      error_ge(whop,newhopcnt);
      walkmap[ni] = 1;
      mapuse[usecnt++] = ni;
      portsbyhop[whop * 2] = dep;
      portsbyhop[whop * 2 + 1] = ni;
      chp->lodur = walkdur(dist,walkspeed);
      chp->dist = dist;
      whop++;
    }

    while (ol && wscnt < shortlim && wlcnt < longlim && whop < newhopcnt) {
      ni = lonsortidx[--ol];
      if (walkmap[ni]) continue;
      parr = ports + ni;
      dist = chkdisto(pdep,parr,wlim_geo);
      if (dist == hi32) break;
      else if (dist == hi32 - 1) continue;
      if (nowalklines && iadrinmap(&net0,dep,ni)) continue;
      if (vosm && nid != hi32 && parr->nidfoot != hi32) dist = mapdist(vosm,FLN,nid,parr->nidfoot,Osfoot,walklimit,pdep,parr,NULL);
      if (dist == hi32) nowalk++;
      if (dist > walklimit) continue;

      if (dist < walklim2) {
        if (wscnt1 > shortlim && rnd(wscnt1) > shortlim) continue;
        wscnt++;
      } else {
        if (wlcnt1 > longlim && rnd(wlcnt1) > longlim) continue;
        wlcnt++;
      }
      chp = newchops + whop;
      error_ge(whop,newhopcnt);
      walkmap[ni] = 1;
      mapuse[usecnt++] = ni;
      portsbyhop[whop * 2] = dep;
      portsbyhop[whop * 2 + 1] = ni;
      chp->lodur = walkdur(dist,walkspeed);
      chp->dist = dist;
      whop++;
    }
    for (use = 0; use < usecnt; use++) {
      ni = mapuse[use];
      walkmap[ni] = 0;
    }
  }

  info(Emp,"\ah%u from \ah%u inferred walk links below \ag%u (%u), range %u-%u",
    whop - thopcnt,newhopcnt - thopcnt,walklimit,walklimit,lodist,hidist);
  info(CC0,"\ah%u links not walkable",nowalk);
  warncc(whop == newhopcnt,Emp,"limited walks at dep %u of %u",dep,portcnt);
  newhopcnt = whop;

  rmiadr(&net0);
  afree0(mapuse);

  if (vosm) osmstats(vosm);

  if (whop == thopcnt) return 0;

  for (whop = thopcnt; whop < newhopcnt; whop++) {
    chp = newchops + whop;
    dep = portsbyhop[whop * 2];
    arr = portsbyhop[whop * 2 + 1];
    chp->kind = Walk;
    chp->ctype = 'W';
    chp->rid = Croute_walk;
    chp->dep = dep;
    chp->arr = arr;
    chp->hidur = chp->lodur;
    error_eq(dep,arr);
    dist = chp->dist;
    hopdist[whop] = dist;
    if (dist < lodist) { lodist = dist; lowhop = whop; }
    if (dist > hidist) { hidist = dist; hiwhop = whop; }
    pdep = ports + chp->dep;
    parr = ports + chp->arr;
    pdep->modes |= Walkbit;
    parr->modes |= Walkbit;
    if (dist < 2) {
      info(Noiter,"whop %u %u-%u nid %u-%u dist %u \ar%f,\ar%f \ar%f,\ar%f %s to %s",whop,dep,arr,pdep->nidfoot,parr->nidfoot,dist,pdep->rlat,pdep->rlon,parr->rlat,parr->rlon,pdep->name,parr->name);
    } else info(Noiter|V0,"whop %u %u-%u dist %u \ar%f,\ar%f \ar%f,\ar%f %s to %s",whop,dep,arr,dist,pdep->rlat,pdep->rlon,parr->rlat,parr->rlon,pdep->name,parr->name);

    chp->dist = dist;
  }

  if (hiwhop < whop) {
    dep = portsbyhop[hiwhop * 2];
    arr = portsbyhop[hiwhop * 2 + 1];
    pdep = ports + dep;
    parr = ports + arr;
    info(0,"longest walk link dist \ag%u hop %u %u-%u \ar%f,\ar%f \ar%f,\ar%f %s to %s",hidist,hiwhop,dep,arr,pdep->rlat,pdep->rlon,parr->rlat,parr->rlon,pdep->iname,parr->name);
  }
  if (lowhop < whop) {
    dep = portsbyhop[lowhop * 2];
    arr = portsbyhop[lowhop * 2 + 1];
    pdep = ports + dep;
    parr = ports + arr;
    info(0,"shortest walk link dist \ag%u hop %u %u-%u \ar%f,\ar%f \ar%f,\ar%f %s to %s",lodist,lowhop,dep,arr,pdep->rlat,pdep->rlon,parr->rlat,parr->rlon,pdep->iname,parr->name);
  }

  char c = 0;
  ub1 hasfrq = 1;
  for (hop = 0; hop < newhopcnt; hop++) {
    chp = newchops + hop;
    switch(chp->kind) {
    case Unknown: return error(0,"hop %u has no type",hop);
    case Airint: c = 'A'; break;
    case Airdom: c = 'a'; break;
    case Rail: c = 'r'; break;
    case Bus: c = 'b'; break;
    case Ferry: c = 'f'; break;
    case Taxi: c = 't'; hasfrq = 0; break;
    case Walk: c = 'w'; hasfrq = 0; break;
    case Kindcnt: return error(0,"hop %u has invalid type",hop);
    }
    chp->ckind = c;
    chp->hasfrq = hasfrq;
    if (hasfrq == 0) continue;
    if (chp->t0 == chp->t1) return error(0,"hop %u no tt range at \ah%u",hop,chp->t0);
  }

  net->whopcnt = newhopcnt;

  net->portsbyhop = portsbyhop;
  net->hopdist = hopdist;
  net->chops = newchops;

  afree(orgportsbyhop,"net");
  afree(orghopdist,"net");
  afree(orgchops,"net");

  return 0;
}

static const ub4 taxinda = 220;
static const ub4 taxireach = 100 * 14000;
static const ub4 taxidistlim = 100 * 80;
static const ub4 taxidistlolim = 100 * 1;

static const ub4 taxidistlim_gnd = 100 * 40;
static const ub4 taxidistlolim_gnd = 100 * 1;

static const ub4 taxidistlim_geo = 100 * 800;
static const ub4 taxidistlolim_geo = 100 * 1;

static int notaxi(struct port *pp,ub4 tnda,ub4 treach)
{
  return ( (pp->modes & Airbit) == 0 && pp->nda <= tnda && pp->sumreach <= treach);
}

static void showmodes(struct network *net)
{
  ub4 dep,portcnt = net->portcnt;
  struct port *pdep,*ports = net->ports;
  ub4 walkcnt = 0,taxicnt = 0,buscnt = 0,railcnt = 0,ferrycnt = 0,airicnt = 0,airdcnt = 0;
  ub4 modes;

  for (dep = 0; dep < portcnt; dep++) {
    pdep = ports + dep;
    modes = pdep->modes;
    if (modes & Walkbit) walkcnt++;
    if (modes & Taxibit) taxicnt++;
    if (modes & Busbit) buscnt++;
    if (modes & Railbit) railcnt++;
    if (modes & Ferrybit) ferrycnt++;
    if (modes & Airintbit) airicnt++;
    if (modes & Airdombit) airdcnt++;
  }
  info(CC0,"\ah%u port\as with walk connections",walkcnt);
  info(CC0,"\ah%u port\as with taxi connections",taxicnt);
  info(CC0,"\ah%u port\as with bus connections",buscnt);
  info(CC0,"\ah%u port\as with rail connections",railcnt);
  info(CC0,"\ah%u port\as with ferry connections",ferrycnt);
  info(CC0,"\ah%u port\as with int air connections",airicnt);
  info(CC0,"\ah%u port\as with dom air connections",airdcnt);
}

static int mkfares(struct network *net)
{
  ub4 hop,thopcnt = net->thopcnt;
  struct chop *hp,*hops = net->chops;
  ub4 fare;
  ub4 farecnt = 0,ifarecnt = 0,nofarecnt = 0;

  for (hop = 0; hop < thopcnt; hop++) {
    hp = hops + hop;
    if (hp->fare) { farecnt++; continue; }
    fare = mkfare(hp);
    if (fare) ifarecnt++; else nofarecnt++;
  }
  return info(0,"\ah%u of \ah%u hops with fares, %u inferred, %u unknown",farecnt,thopcnt,ifarecnt,nofarecnt);
}

static int mktaxi(struct network *net)
{
  ub4 portcnt = net->portcnt;
  ub4 chopcnt = net->chopcnt;
  struct port *pdep,*parr,*parr2,*ports = net->ports;
  char *dname;
  ub4 dist,lodist = hi32,hidist = 0;
  ub4 dep,arr;
  ub4 thop,thopcnt = 0,thopcnt2 = 0;
  ub4 lohop = 0,hihop = 0;
  ub4 dur = 0;
  ub4 run;
  int onair,ongeo,onda,onreach;
  ub4 tlimit,tdistlim,tdistlolim,tlim4,tnda,treach;
  ub4 tdepcnt = 0,onaircnt = 0,ondacnt = 0,onreachcnt = 0,ongeocnt = 0;
  double wlim_geo = 100 * 100;
  ub4 depnid,arrnid;
  void *vosm = net->vosm;

  ub4 taxilimit = globs.taxilimit;
  ub4 taxilimit_gnd = globs.taxilimitgnd;

  net->thopcnt = chopcnt;

  if (globs.notaxi) return info0(0,"taxi links disabled in cfg");
  if (taxilimit == 0) return info0(0,"no taxi links");

  struct eta eta;

  ub4 *latsort = net->latsort;
  ub4 *lonsort = net->lonsort;
  ub4 *latsortidx = net->latsortidx;
  ub4 *lonsortidx = net->lonsortidx;

  ub4 nonid = 0;
  int dbg = 0;
  int rv;

  ub4 nda;
  ub8 sumreach;

  ub4 *nid2port = NULL;
  ub1 *portdup = NULL;
  ub4 *portlst = NULL;
  ub4 *rportlst = NULL;
  ub8 *portdts = NULL;
  ub8 *rportdts = NULL;
  ub1 *newlst = NULL;
  ub8 *ndasort,*reachsort,*distsort,*sdistsort,*dursort;
  ndasort = reachsort = distsort = sdistsort = dursort = NULL;

  ub4 nidcnt = 0;
  if (vosm && useprofile) {
    nidcnt = net->nidcnt;
    nid2port = talloc0(nidcnt,ub4,0);
    portdup = talloc0(portcnt,ub1,0);
    portdts = talloc0(portcnt,ub8,0);
    rportdts = talloc0(portcnt,ub8,0);
    portlst = talloc0(portcnt,ub4,0);
    rportlst = talloc0(portcnt,ub4,0);
    newlst = talloc0(portcnt,ub1,0);
    ndasort = talloc0(portcnt,ub8,0);
    reachsort = talloc0(portcnt,ub8,0);
    distsort = talloc0(portcnt,ub8,0);
    sdistsort = talloc0(portcnt,ub8,0);
    dursort = talloc0(portcnt,ub8,0);
  }

  // lookup osm nid per port
  for (dep = 0; dep < portcnt; dep++) {
    if (progress(&eta,"taxi links pass 1 port %u of %u %u links",dep,portcnt,thopcnt)) return 1;

    pdep = ports + dep;
    if (pdep->valid == 0) continue;
    dname = pdep->iname;
    ongeo = pdep->geo;
    onair = (pdep->modes & Airbit);
    tlimit = onair ? taxilimit : taxilimit_gnd;
    nda = pdep->nda;
    sumreach = pdep->sumreach;
    onda = (nda > taxinda);
    onreach = (sumreach > taxireach);
    infocc(dbg,0,"port %u onair %d onda %d onreach %d %s",dep,onair,onda,onreach,dname);

    if (vosm) {
      depnid = lookupnid(vosm,pdep->lat * 10,pdep->lon * 10,Oscar,&dist);
      if (depnid == hi32) nonid++;
      infocc(dist > 10 * 100,Iter,"port %u dist \ag%u %s",dep,dist,pdep->iname);
      if (dist > 60 * 100) {
        depnid = hi32;
        info(0,"port %u off-map dist \ag%u %s",dep,dist,pdep->iname);
      }
      if (depnid != hi32 && nid2port) {
        error_ge(depnid,nidcnt);
        if (nid2port[depnid] == 0) nid2port[depnid] = dep + 1;
      } else if (depnid == hi32 && nid2port) continue;
    } else depnid = hi32;
    pdep->nidcar = depnid;
    if (onair == 0 && ongeo == 0 && onda == 0 && onreach == 0) continue;
    tdepcnt++;
    pdep->taxi = 1;

    if (ongeo) ongeocnt++;
    if (onair) onaircnt++;
    if (onda) ondacnt++;
    if (onreach) onreachcnt++;
    infocc(dbg,0,"port %u nid %u onair %d onda %d onreach %d %s",dep,depnid,onair,onda,onreach,dname);
    if (useprofile) thopcnt += max(12,tlimit) * 2;
    else thopcnt += tlimit * 2;
  }
  info(0,"\ah%u tentative inferred taxi links for \ah%u of \ah%u ports",thopcnt,tdepcnt,portcnt);
  info(0," \ah%u air  \ah%u geo  \ah%u da %u  \ah%u reach %u",onaircnt,ongeocnt,ondacnt,taxinda,onreachcnt,taxireach);
  info(CC0,"\ah%u of \ah%u ports not on map",nonid,tdepcnt);
  if (thopcnt == 0) return 0;

  ub4 *orgportsbyhop = net->portsbyhop;
  ub4 *orghopdist = net->hopdist;
  struct chop *orgchops = net->chops;

  ub4 newhopcnt = chopcnt + thopcnt;

  ub4 *portsbyhop = alloc(newhopcnt * 2,ub4,0,"net portsbyhop",newhopcnt);
  memcpy(portsbyhop,orgportsbyhop,chopcnt * 2 * sizeof(ub4));

  ub4 *hopdist = alloc(newhopcnt,ub4,0,"net hopdist",newhopcnt);
  memcpy(hopdist,orghopdist,chopcnt * sizeof(ub4));

  struct chop *chp,*chops = alloc(newhopcnt,struct chop,0,"net chop",0);
  memcpy(chops,orgchops,chopcnt * sizeof(struct chop));

  // filter duplicates
  iadrbase tnet;
  oclear(tnet);
  if (mkiadr0(&tnet,portcnt,portcnt,ub2,20000,16,"net0")) return 1;
  if (mkiadrmap(&tnet,"net taximap")) return 1;

  ub4 a,o,al,ar,ol,or,ni,cnt,rcnt;
  ub4 dlat,dlon;

  struct osmres res;
  ub4 n,n2;
  ub8 sumdist,reach,portdt;

  for (dep = 0; dep < portcnt; dep++) {
    if (progress(&eta,"taxi links pass 2 port %u of %u %u links",dep,portcnt,thopcnt2)) return 1;
    pdep = ports + dep;
    if (pdep->taxi == 0) continue;
    dname = pdep->iname;
    info(V0,"port %u %s to",dep,dname);
    infocc(dbg,0,"port %u %s",dep,dname);

    onair = (pdep->modes & Airbit);
    if (pdep->geo) {
      tlimit = taxilimit_gnd;
      tdistlim = taxidistlim_geo;
      tdistlolim = taxidistlolim_geo;
    } else if (onair) {
      tlimit = taxilimit;
      tdistlim = taxidistlim;
      tdistlolim = taxidistlolim;
    } else {
      tlimit = taxilimit_gnd;
      tdistlim = taxidistlim_gnd;
      tdistlolim = taxidistlolim_gnd;
    }
    wlim_geo = tdistlim;
    tlim4 = tlimit / 4;

    onair = (pdep->modes & Airbit);
    tnda = taxinda;
    treach = taxireach;

    dlat = pdep->lat; dlon = pdep->lon;
    depnid = pdep->nidcar;

    if (vosm && useprofile) {
      error_lt(tlimit,2);
      if (depnid == hi32) continue;
      rv = osmprofile(vosm,depnid,nid2port,portdup,portcnt,rportlst,rportdts,tdistlim * 4,0,&res);
      if (rv) continue;
      rcnt = res.cnt;
      if (rcnt == 0) {
        warncc(onair,0,"airport %u has no taxi links %s",dep,dname);
        continue;
      }

      cnt = 0;
      for (n = 0; n < rcnt; n++) {
        arr = rportlst[n];
        if (iadrinmap(&tnet,dep,arr)) continue;
        portdt = rportdts[n];
        dist = (ub4)(portdt >> 32);
        if (dist > tdistlim || dist < tdistlolim) continue;
        portdts[cnt] = portdt;
        portlst[cnt++] = arr;
      }

      if (cnt == 0) {
        warncc(onair,0,"airport %u has no taxi links %s",dep,dname);
        continue;
      } else if (cnt <= tlimit) {
        for (n = 0; n < cnt; n++) newlst[n] = (ub1)(n+1);
      } else {
        for (n = 0; n < cnt; n++) {
          newlst[n] = 0;
          arr = portlst[n];
          error_ge(arr,portcnt);
          parr = ports + arr;
          nda = parr->nda;
          reach = parr->msbreach;

          portdt = portdts[n];
          dist = (ub4)(portdt >> 32);
          dur = portdt & hi32;

          parr = ports + arr;

          info(Iter," %u link %s - %s dist \ag%u dur %u",n,pdep->iname,parr->iname,dist,dur);

          ndasort[n] = ((ub8)nda << 32) | n;
          reachsort[n] = ((ub8)reach << 32) | n;
          distsort[n] = ((ub8)dist << 32) | n;
          dursort[n] = ((ub8)dur << 32) | n;

          // cumulative distance
          sumdist = 0;
          for (n2 = 0; n2 < cnt; n2++) {
            if (n == n2) continue;
            parr2 = ports + portlst[n2];
            sumdist += fgeodist(parr,parr2,0);
          }
          if (sumdist > hi32) { warn(0,"dist sum \ah%lu for %s - %s",sumdist,pdep->iname,parr->iname); sumdist = hi32; }
          sdistsort[n] = ((sumdist / dist) << 32) | n;
        }
        fsort8(ndasort,cnt,0,FLN,"nda");
        fsort8(reachsort,cnt,0,FLN,"reach");
        fsort8(distsort,cnt,0,FLN,"dist");
        fsort8(sdistsort,cnt,0,FLN,"sdist");
        fsort8(dursort,cnt,0,FLN,"dur");

        // take top-2 from each aspect
        newlst[ndasort[cnt - 1] & hi32] = 1;
        newlst[ndasort[cnt - 2] & hi32] = 2;
        newlst[reachsort[cnt - 1] & hi32] = 3;
        newlst[reachsort[cnt - 2] & hi32] = 4;
        newlst[distsort[0] & hi32] = 5;
        newlst[distsort[1] & hi32] = 6;
        newlst[dursort[0] & hi32] = 7;
        newlst[dursort[1] & hi32] = 8;
        newlst[sdistsort[cnt - 1] & hi32] = 9;
        newlst[sdistsort[cnt - 2] & hi32] = 10;
      }
      for (n = 0; n < cnt; n++) {
        if (newlst[n] == 0) continue;
        error_ge(thopcnt2+1,thopcnt);
        arr = portlst[n];
        portdt = portdts[n];
        dist = (ub4)(portdt >> 32);
        dur = portdt & hi32;

        chp = chops + chopcnt + thopcnt2;
        error_nz(chp->dep,thopcnt2);
        chp->dep = dep;
        chp->arr = arr;
        chp->dist = dist;
        chp->lodur = dur;
        thopcnt2++;

        iadrinc(&tnet,dep,arr,0);

        parr = ports + arr;

        info(0,"%u,%u taxi link %s - %s dist \ag%u dur %u",n,newlst[n],pdep->iname,parr->iname,dist,dur);

        if (iadrinmap(&tnet,arr,dep)) continue;

        chp = chops + chopcnt + thopcnt2;
        error_nz(chp->dep,thopcnt2);
        chp->dep = arr;
        chp->arr = dep;
        chp->dist = dist;
        chp->lodur = dur;
        thopcnt2++;
        iadrinc(&tnet,arr,dep,0);
      }
      continue;
    }

    if (vosm) {
      error_nz(useprofile,dep);
    }

    a = bsearch4(latsort,portcnt,dlat,FLN,dname);
    o = bsearch4(lonsort,portcnt,dlon,FLN,dname);

    cnt = 0;


  for (run = 0; run < 10 && cnt < 2 * tlim4; run++) {
    ar = a;
    or = o;
    al = a + 1;
    ol = o + 1;

    while (ar < portcnt && cnt < tlim4) {
      ni = latsortidx[ar++];
      if (ni == dep) continue;
      parr = ports + ni;
      if (notaxi(parr,tnda,treach)) continue;
      if (iadrinmap(&tnet,dep,ni)) continue;

      arrnid = parr->nidcar;
      dist = chkdista(pdep,parr,wlim_geo);
      infocc(dbg,0,"%u-%u run %u dist \ag%u %s-%s",dep,ni,run,dist,dname,parr->iname);
      if (dist == hi32) break;
      else if (dist == hi32 - 1) continue;
      info(V0,"  %u %s",ni,parr->iname);
      dur = dist / 80; // placeholder in case out of map range
      if (vosm && depnid != hi32 && arrnid != hi32) dist = mapdist(vosm,FLN,depnid,arrnid,Oscar,tdistlim,pdep,parr,&dur);
      if (dist > tdistlim || dist < tdistlolim) {
        infocc(dbg || dist == hi32,0,"%u-%u dist \ag%u nid %u-%u %s-%s",dep,ni,dist,depnid,arrnid,dname,parr->iname);
        continue;
      }
      infocc(Msgrep,Noiter,"%u-%u dist \ag%u dur %u \ar%f,\ar%f \ar%f,\ar%f %s to %s",dep,ni,dist,dur,pdep->rlat,pdep->rlon,parr->rlat,parr->rlon,pdep->iname,parr->iname);

      chp = chops + chopcnt + thopcnt2;
      error_nz(chp->dep,thopcnt2);
      chp->dep = dep;
      chp->arr = ni;
      chp->dist = dist;
      chp->lodur = dur;
      iadrinc(&tnet,dep,ni,0);
      cnt++;
      thopcnt2++;

      if (iadrinmap(&tnet,ni,dep)) continue;

      // reverse direction
      chp++;
      chp->dep = ni;
      chp->arr = dep;
      chp->dist = dist;
      chp->lodur = dur;
      iadrinc(&tnet,ni,dep,0);
      thopcnt2++;
    }

    while (al && cnt < 2 * tlim4) {
      ni = latsortidx[--al];
      if (ni == dep) continue;
      parr = ports + ni;
      if (notaxi(parr,tnda,treach)) continue;
      if (iadrinmap(&tnet,dep,ni)) continue;

      arrnid = parr->nidcar;
      dist = chkdista(pdep,parr,wlim_geo);
      infocc(dbg,0,"%u-%u dist \ag%u nid %u-%u %s-%s",dep,ni,dist,depnid,arrnid,dname,parr->iname);
      if (dist == hi32) break;
      else if (dist == hi32 - 1) continue;
      info(V0,"  %u %s",ni,parr->iname);
      dur = dist / 80;

      if (vosm && depnid != hi32 && arrnid != hi32) dist = mapdist(vosm,FLN,depnid,arrnid,Oscar,tdistlim,pdep,parr,&dur);
      if (dist > tdistlim || dist < tdistlolim) {
        infocc(dbg || dist == hi32,0,"%u-%u dist \ag%u nid %u-%u %s-%s",dep,ni,dist,depnid,arrnid,dname,parr->iname);
        continue;
      }

      infocc(Msgrep,Noiter,"%u-%u dist \ag%u dur %u \ar%f,\ar%f \ar%f,\ar%f %s to %s",dep,ni,dist,dur,pdep->rlat,pdep->rlon,parr->rlat,parr->rlon,pdep->iname,parr->iname);

      chp = chops + chopcnt + thopcnt2;
      chp->dep = dep;
      chp->arr = ni;
      chp->dist = dist;
      chp->lodur = dur;
      iadrinc(&tnet,dep,ni,0);
      cnt++;
      thopcnt2++;

      if (iadrinmap(&tnet,ni,dep)) continue;

      // reverse direction
      chp++;
      chp->dep = ni;
      chp->arr = dep;
      chp->dist = dist;
      chp->lodur = dur;
      iadrinc(&tnet,ni,dep,0);
      thopcnt2++;
    }

    while (or < portcnt && cnt < 3 * tlim4) {
      ni = lonsortidx[or++];
      if (ni == dep) continue;
      parr = ports + ni;
      if (notaxi(parr,tnda,treach)) continue;
      if (iadrinmap(&tnet,dep,ni)) continue;

      arrnid = parr->nidcar;
      dist = chkdisto(pdep,parr,wlim_geo);
      infocc(dbg,0,"%u-%u dist \ag%u %s-%s",dep,ni,dist,dname,parr->iname);
      if (dist == hi32) break;
      else if (dist == hi32 - 1) continue;
      info(V0,"  %u %s",ni,parr->iname);
      dur = dist / 80;

      if (vosm && depnid != hi32 && arrnid != hi32) dist = mapdist(vosm,FLN,depnid,arrnid,Oscar,tdistlim,pdep,parr,&dur);
      if (dist > tdistlim || dist < tdistlolim) {
        infocc(dbg || dist == hi32,0,"%u-%u dist \ag%u nid %u-%u %s-%s",dep,ni,dist,depnid,arrnid,dname,parr->iname);
        continue;
      }
      infocc(Msgrep,Noiter,"%u-%u dist \ag%u dur %u \ar%f,\ar%f \ar%f,\ar%f %s to %s",dep,ni,dist,dur,pdep->rlat,pdep->rlon,parr->rlat,parr->rlon,pdep->iname,parr->iname);

      chp = chops + chopcnt + thopcnt2;
      chp->dep = dep;
      chp->arr = ni;
      chp->dist = dist;
      chp->lodur = dur;
      iadrinc(&tnet,dep,ni,0);
      cnt++;
      thopcnt2++;

      if (iadrinmap(&tnet,ni,dep)) continue;

      // reverse direction
      chp++;
      chp->dep = ni;
      chp->arr = dep;
      chp->dist = dist;
      chp->lodur = dur;
      iadrinc(&tnet,ni,dep,0);
      thopcnt2++;
    }

    while (ol && cnt < tlimit) {
      ni = lonsortidx[--ol];
      if (ni == dep) continue;
      parr = ports + ni;
      if (notaxi(parr,tnda,treach)) continue;
      if (iadrinmap(&tnet,dep,ni)) continue;

      arrnid = parr->nidcar;
      dist = chkdisto(pdep,parr,wlim_geo);
      infocc(dbg,0,"%u-%u dist \ag%u %s-%s",dep,ni,dist,dname,parr->iname);
      if (dist == hi32) break;
      else if (dist == hi32 - 1) continue;
      info(V0,"  %u %s",ni,parr->iname);
      dur = dist / 80;

      if (vosm && depnid != hi32 && arrnid != hi32) dist = mapdist(vosm,FLN,depnid,arrnid,Oscar,tdistlim,pdep,parr,&dur);
      infocc(dbg,0,"%u-%u dist \ag%u %s-%s",dep,ni,dist,dname,parr->iname);
      if (dist > tdistlim || dist < tdistlolim) {
        infocc(dbg || dist == hi32,0,"%u-%u dist \ag%u nid %u-%u %s-%s",dep,ni,dist,depnid,arrnid,dname,parr->iname);
        continue;
      }
      infocc(Msgrep,Noiter,"%u-%u dist \ag%u dur %u \ar%f,\ar%f \ar%f,\ar%f %s to %s",dep,ni,dist,dur,pdep->rlat,pdep->rlon,parr->rlat,parr->rlon,pdep->iname,parr->iname);

      chp = chops + chopcnt + thopcnt2;
      chp->dep = dep;
      chp->arr = ni;
      chp->dist = dist;
      chp->lodur = dur;
      iadrinc(&tnet,dep,ni,0);
      cnt++;
      thopcnt2++;

      if (iadrinmap(&tnet,ni,dep)) continue;

      // reverse direction
      chp++;
      chp->dep = ni;
      chp->arr = dep;
      chp->dist = dist;
      chp->lodur = dur;
      iadrinc(&tnet,ni,dep,0);
      thopcnt2++;
    }
    error_gt(thopcnt2,thopcnt,0);
    tnda /= 2;
    treach /= 2;
   } // each run
   if (cnt == 0 && onair) warn(0,"airport %u has no taxi links %s",dep,dname);
  }

  if (vosm) {
    osmstats(vosm);
    if (nid2port) {
      afree0(nid2port);
    }
  }

  info(Emp,"\ah%u from \ah%u inferred taxi links for \ah%u of \ah%u ports",thopcnt2,thopcnt,tdepcnt,portcnt);

  rmiadr(&tnet);

  if (thopcnt2 == 0) return 0;

  // fill basics
  for (thop = chopcnt; thop < chopcnt + thopcnt2; thop++) {
    chp = chops + thop;

    dep = chp->dep;
    arr = chp->arr;
    portsbyhop[thop * 2] = dep;
    portsbyhop[thop * 2 + 1] = arr;
    pdep = ports + dep;
    parr = ports + arr;
    pdep->modes |= Taxibit;
    parr->modes |= Taxibit;

    chp->kind = Taxi;
    chp->rid = hi32;
    chp->ctype = 'T';

    dist = chp->dist;
    hopdist[thop] = dist;
    if (dist < lodist) { lodist = dist; lohop = thop; }
    if (dist > hidist) { hidist = dist; hihop = thop; }

    dur = chp->lodur;
    chp->hidur = dur;
    info(0,"%u-%u \ag%u %u min nid %u-%u %s to %s",dep,arr,dist,dur,pdep->nidcar,parr->nidcar,pdep->name,parr->name);
    info(0,"  \ar%f,\ar%f \ar%f,\ar%f %s to %s",pdep->rlat,pdep->rlon,parr->rlat,parr->rlon,pdep->prefix,parr->prefix);
  }

  chp = chops + lohop;
  dep = chp->dep;
  arr = chp->arr;
  pdep = ports + dep;
  parr = ports + arr;
  info(0,"shortest taxi link \ag%u \ar%f,\ar%f \ar%f,\ar%f %s to %s",lodist,pdep->rlat,pdep->rlon,parr->rlat,parr->rlon,pdep->iname,parr->iname);
  chp = chops + hihop;
  dep = chp->dep;
  arr = chp->arr;
  pdep = ports + dep;
  parr = ports + arr;
  info(0,"longest taxi link \ag%u \ar%f,\ar%f \ar%f,\ar%f %s to %s",hidist,pdep->rlat,pdep->rlon,parr->rlat,parr->rlon,pdep->iname,parr->iname);

  newhopcnt = chopcnt + thopcnt2;

  net->thopcnt = newhopcnt;

  net->portsbyhop = portsbyhop;
  net->hopdist = hopdist;
  net->chops = chops;

  afree(orgportsbyhop,"net");
  afree(orghopdist,"net");
  afree(orgchops,"net");

  return 0;
}

// get lowest transfer time per connecting base hop pair
change to use estdur, which in turn uses regular search
store results, use for net1 estdur
static int mklotx(struct network *net)
{
  ub4 h,h1,h2,hcnt,hopcnt = net->hopcnt;
  struct chop *hp,*hp2,*hops = net->chops;
  ub4 *portsbyhop = net->portsbyhop;
  ub4 dep,arr,i;
  ub4 lotx,hitx;
  ub8 x;
  struct eta eta;
  ub8 *hopsbyxdep = talloc(hopcnt,ub8,0,"net x",0);
  iadrbase *hoptx = &net->hoptx;
  ub8 txcnt = 0,eqtxcnt = 0;

  h = 0;
  for (h1 = 0; h1 < hopcnt; h1++) {
    hp = hops + h1;
    if (hp->kind == Taxi || hp->evcnt == 0) continue;
    dep = portsbyhop[h1 * 2];
    x = (ub8)dep << 32 | h1;
    hopsbyxdep[h++] = x;
  }
  hcnt = h;
  info(0,"\ah%u tx candidates",hcnt);
  error_z(hcnt,hopcnt);
  sort8(hopsbyxdep,hcnt,FLN,"x");

  ub4 *hopsbydep = talloc(hcnt,ub4,0,"net",0);
  ub4 *hopsdep = talloc(hcnt,ub4,0,"net",0);
  for (h = 0; h < hcnt; h++) {
    x = hopsbyxdep[h];
    hopsbydep[h] = (ub4)(x >> 32);
    hopsdep[h] = x & hi32;
  }
  afree0(hopsbyxdep);

  if (mkiadr0(hoptx,hopcnt,hopcnt,ub2,10000,16,"hoptx")) return 1;

  for (h = 0; h < hcnt; h++) {
    if (progress0(&eta,"pass 1 min tx hop %u of %u",h,hcnt)) return 1;
    h1 = hopsdep[h];
    hp = hops + h1;
    dep = hp->dep;
    arr = hp->arr;
    i = bsearch4(hopsbydep,hcnt,arr,FLN,"x");
    if (i >= hcnt) { info(Iter,"no connect for hop %u arr %u",h1,arr); continue; }
    if (hopsbydep[i] != arr) { info(Iter,"no connect for hop %u arr %u",h1,arr); continue; }
    info(Iter|Notty,"connect %u-%u at %u",h1,hopsdep[i],i);
    // while (i && hopsbydep[i] == arr) i--;
    while (i < hcnt && hopsbydep[i] == arr) {
      h2 = hopsdep[i++];
      hp2 = hops + h2;
      if (hp->rid == hp2->rid || hp2->arr == dep) continue;
      iadrinc(hoptx,h1,h2,0);
      txcnt++;
    }
  }
  info(0,"\ah%lu tx pairs",txcnt);
  if (mkiadr1(hoptx)) return 1;

  for (h = 0; h < hcnt; h++) {
    if (progress0(&eta,"pass 2 min tx hop %u of %u",h,hcnt)) return 1;
    h1 = hopsdep[h];
    hp = hops + h;
    if (hp->kind == Taxi || hp->evcnt == 0) continue;
    dep = hp->dep;
    arr = hp->arr;
    i = bsearch4(hopsbydep,hcnt,arr,FLN,"x");
    if (i >= hcnt) continue;
    if (hopsbydep[i] != arr) continue;
    // while (i && hopsbydep[i-i] == arr) i--;
    while (i < hcnt && hopsbydep[i] == arr) {
      h2 = hopsdep[i++];
      hp2 = hops + h2;
      if (hp->rid == hp2->rid || hp2->arr == dep) continue;
      lotx = lotx2(net,h,h2,&hitx);
      if (lotx == hi32) lotx = hi16;
      wriadr2(hoptx,h,h2,(ub2)lotx);
      if (lotx == hitx) eqtxcnt++;
    }
  }
  finiadr(hoptx);
  afree0(hopsdep);
  afree0(hopsbydep);
  info(CC0,"\ah%lu of \ah%lu pairs with constant transfer time",eqtxcnt,txcnt);
  return 0;
}

// check single port connectivity
static ub4 chkcon(lnet *net,ub4 dep,ub4 lim,ub4 iterlim,ub1 *conns)
{
  ub4 prvcnt,concnt = 0;
  ub4 iter = 0,iterhi = 0;
  ub4 arr,dep1,darr;
  ub4 portcnt = net->portcnt;
  struct port *pdep,*pdep1,*parr,*ports = net->ports;

  ub4 *dlst,*deplst = net->deplst[0];

  pdep = ports + dep;
  int notx = (pdep->infconcnt != hi32); //no lotx on second pass

  ub4 depcnt = pdep->depcnt[0];
  ub4 depofs = pdep->depofs[0];
  ub4 *txreach = pdep->txreach;

  ub4 seq2,seq1 = pdep->gridseq;
  ub4 gseqcnt = net->seqdlen;
  ub8 seq1cnt = (ub8)seq1 * gseqcnt;

  ub1 lo,*seqlotx = net->seqlotx;

  dlst = deplst + depofs;

  nclear(conns,portcnt);

  // direct links
  for (darr = 0; darr < depcnt; darr++) {
    arr = dlst[darr] & Nbrmask;
    if (dep == arr) continue;
    conns[arr] = 1; concnt++;
    if (notx) continue;
    txreach[0]++;
    parr = ports + arr;
    seq2 = parr->gridseq;
    seqlotx[seq1cnt + seq2] = 0;
  }

  do {
    prvcnt = concnt;
    iter++;

    iterhi = max(iterhi,iter);

    // subsequent indirect links
    for (dep1 = 0; dep1 < portcnt; dep1++) {
      if (conns[dep1] != 1) continue;

      pdep1 = ports + dep1;
      depcnt = pdep1->depcnt[0];
      depofs = pdep1->depofs[0];
      dlst = deplst + depofs;

      for (darr = 0; darr < depcnt; darr++) {
        arr = dlst[darr] & Nbrmask;
        if (conns[arr] || dep == arr) continue;
        conns[arr] = 1; concnt++;
        if (notx) continue;
        parr = ports + arr;
        seq2 = parr->gridseq;
        lo = seqlotx[seq1cnt + seq2];
        if (iter < lo) seqlotx[seq1cnt + seq2] = (ub1)iter;
      }
      conns[dep1] = 2;
      if (concnt > lim) break;
    }
    if (iter < Nstop) txreach[iter] += (concnt - prvcnt);

    if (concnt > portcnt) { error(0,"concnt %u portcnt %u",concnt,portcnt); return concnt; }

  } while (concnt > prvcnt && concnt < lim && iter < iterlim);

  if (pdep->infconcnt == hi32 || concnt > pdep->infconcnt) {
    pdep->infconcnt = concnt;
    pdep->infiter = iter;
  }
  return concnt;
}

// assess connectivity
static int conchk(struct network *net)
{
  int doconchk = globs.engvars[Eng_conchk];
  ub4 portcnt = net->portcnt;
  ub4 vportcnt = net->vportcnt;

  struct port *pdep,*parr,*ports = net->ports;

  ub4 dep,arr;

  ub4 gseqcnt = net->seqdlen;
  ub1 lotx,*seqlotx = net->seqlotx;
  ub8 seq,seqd,seqa,seq2 = (ub8)gseqcnt * gseqcnt;

  if (seqlotx == NULL) doconchk = 0;

  nsethi(seqlotx,seq2);

  for (dep = 0; dep < portcnt; dep++) {
    pdep = ports + dep;
    pdep->infconcnt = hi32;
  }

  if (doconchk == 0) {
    info0(0,"skip connectivity check");
    return 0;
  }

  ub1 *conns = talloc(portcnt,ub1,0,"net dotlinks",portcnt);
  ub1 *hiconns = talloc(portcnt,ub1,0,"net dotlinks",portcnt);
  ub1 *hiconns2 = talloc(portcnt,ub1,0,"net dotlinks",portcnt);
  ub4 *constats = talloc(portcnt+1,ub4,0,"net constats",portcnt);

  ub4 cnt,concnt = 0;
  ub4 iter = 0,iterhi = 0, iterlim = 10;
  double lat,lon;
  struct eta eta;

  ub4 lolim = max(100,portcnt / 10);
  if (portcnt > 25000) lolim = min(lolim,500);
  else if (portcnt < 1000) lolim = portcnt;

  if (doconchk & 4) {
    lolim = portcnt;
    iterlim = Nstop * 2;
    net->havelotx = 1;
  }

  // lowest connected ports
  info(0,"show lowest infconnect for limit %u",lolim);
  for (dep = 0; dep < portcnt && (doconchk & 1); dep++) {
    if (progress(&eta,"port %u of %u+ conns %u at %u",dep,portcnt,concnt,iter)) return 1;
    pdep = ports + dep;
    if (pdep->valid == 0) continue;

    concnt = chkcon(net,dep,lolim,iterlim,conns);
    constats[concnt]++;
    iter = pdep->infiter;
    iterhi = max(iterhi,iter);
    if (concnt + 1 >= lolim) continue;

    lat = pdep->rlat * 180/ M_PI;
    lon = pdep->rlon * 180/ M_PI;
    infocc(concnt * 2 < portcnt,Noiter,"port %u cons %u/%u from %u at iter %u %f %f %s",dep,concnt,pdep->infconcnt,lolim,iter,lat,lon,pdep->iname);
    if (portcnt > 1000 && concnt * 100 < portcnt) pdep->valid = 0;
  }

  ub4 cumcnt = 0;
  for (concnt = 0; concnt < portcnt; concnt++) {
    cnt = constats[concnt];
    cumcnt += cnt;
    infocc(cnt,Noiter|Notty,"conn %u %u %u%%",concnt,cnt,(cumcnt * 100) / portcnt);
  }

  ub1 ltlo = 0xff,lthi = 0;
  ub8 noltcnt = 0;

  if (doconchk & 4) {
    for (seq = 0; seq < seq2; seq++) {
      lotx = seqlotx[seq];
      if (lotx == 0xff) {
        pdep = parr = ports;
        seqd = seq / gseqcnt;
        seqa = seq % gseqcnt;
        for (dep = 0; dep < portcnt; dep++) {
          pdep = ports + dep;
          if (pdep->gridseq == seqd) break;
        }
        if (dep == portcnt) warn(0,"grid cell %lu not found",seqd);
        for (arr = 0; arr < portcnt; arr++) {
          parr = ports + arr;
          if (parr->gridseq == seqa) break;
        }
        if (arr == portcnt) warn(0,"grid cell %lu not found",seqa);
        info(0,"no lotx at grid %lu,%lu %s %s",seqd,seqa,pdep->iname,parr->iname);
        noltcnt++;
        continue;
      }
      ltlo = min(lotx,ltlo);
      lthi = max(lotx,lthi);
    }
    info(Emp,"lotx lo %u hi %u none \ah%lu",ltlo,lthi,noltcnt);
  }

  if ( (doconchk & 2) == 0) {
    dep = 0;
    lolim = hi32;
    concnt = chkcon(net,dep,lolim,iterlim,conns);
    pdep = ports + dep;
    info(Emp,"port 0 conns %u of %u = %u at iter %u",concnt,portcnt,portcnt - concnt,pdep->infiter);
    return 0;
  }

  // sample highest conn
  nclear(constats,portcnt+1);
  ub4 sampleiv = max(portcnt / 50,1);
  if (portcnt > 100000) sampleiv = portcnt / 20;
  ub4 hicon = 0,hicon2 = 0;
  lolim = hi32;

  for (dep = 0; dep < portcnt; dep += sampleiv) {
    if (progress(&eta,"port %u of %u conns %u",dep,portcnt,concnt)) return 1;
    pdep = ports + dep;
    if (pdep->valid == 0) continue;

    concnt = chkcon(net,dep,lolim,iterlim,conns);
    iter = pdep->infiter;
    iterhi = max(iterhi,iter);
    iterhi = max(iterhi,pdep->infiter);
    if (concnt > hicon) {
      hicon = concnt;
      memcpy(hiconns,conns,portcnt);
    } else if (concnt > hicon2 && concnt * 2 < hicon) {
      hicon2 = concnt;
      memcpy(hiconns2,conns,portcnt);
    }
    constats[concnt]++;
    lat = pdep->rlat * 180/ M_PI;
    lon = pdep->rlon * 180/ M_PI;
    info(Noiter,"port %u of %u conns %u of %u iter %u %f %f %s",dep,vportcnt,concnt,hicon,iter,lat,lon,pdep->iname);
  }

  info(0,"highest conn %u of %u iter %u",hicon,vportcnt,iterhi);

 // display list of ports not in hicon group ( largest island )
  if (portcnt < 10000) lolim = hi32;
  else if (portcnt < 40000) lolim = hicon / 2;
  else lolim = 2000;

  info0(User,"");
  info(0,"ports not in %u-conn",hicon);

  for (arr = 0; arr < portcnt; arr++) {
    if (globs.sigint) return 1;
    if (hiconns[arr]) continue;
    parr = ports + arr;
    if (parr->valid == 0) continue;
    if (parr->infconcnt * 2 > hicon) continue;
    concnt = chkcon(net,arr,lolim,iterlim,conns);
    lat = parr->rlat * 180/ M_PI;
    lon = parr->rlon * 180/ M_PI;
    info(Noiter,"  port %u cnt %u/%u iter %u %f %f %s",arr,concnt,parr->infconcnt,parr->infiter,lat,lon,parr->iname);
  }

  info0(User,"");
  info(0,"ports not in %u-conn",hicon2);

 // display list of ports not in hicon2 group ( second largest island )
  for (arr = 0; arr < portcnt && portcnt < 40000; arr++) {
    if (globs.sigint) return 1;
    if (hiconns2[arr] || hiconns[arr]) continue;
    parr = ports + arr;
    if (parr->valid == 0) continue;
    if (parr->infconcnt * 2 > hicon2) continue;
    concnt = chkcon(net,arr,lolim,iterlim,conns);
    lat = parr->rlat * 180/ M_PI;
    lon = parr->rlon * 180/ M_PI;
    info(Noiter,"  port %u/%u cnt %u iter %u %f %f %s",arr,concnt,parr->infconcnt,parr->infiter,lat,lon,parr->iname);
  }

  cumcnt = 0;
  for (concnt = 0; concnt < portcnt; concnt++) {
    cnt = constats[concnt];
    cumcnt += cnt;
    infocc(cnt,Noiter,"conn %u %u %u%%",concnt,cnt,(cumcnt * 100) / portcnt);
  }

  cumcnt = 0;
  for (concnt = 0; concnt < portcnt && cumcnt < 1000; concnt++) {
    cnt = constats[concnt];
    if (cnt == 0) continue;
    cumcnt += cnt;
    for (dep = 0; dep < portcnt; dep++) {
      pdep = ports + dep;
      if (pdep->infconcnt != cnt) continue;
      info(Noiter,"port %u cons %u %s",dep,cnt,pdep->iname);
    }
  }

  // search for closest pair of hicon and hicon2 members
  ub4 lodep,loarr;
  ub4 dist,lodist;
  lodep = loarr = hi32;
  lodist = hi32;
  for (dep = 0; dep < portcnt; dep++) {
    pdep = ports + dep;
    if (pdep->infconcnt <= hicon2) continue;

    for (arr = 0; arr < portcnt; arr++) {
      if (arr == dep) continue;
      parr = ports + arr;
      if (parr->infconcnt > hicon2 || parr->infconcnt * 2 < hicon2) continue;

      dist = fgeodist(pdep,parr,1);
      if (dist < lodist) {
        lodep = dep; loarr = arr;
        lodist = dist;
      }
    }
  }
  if (lodep == hi32) return 0;
  pdep = ports + lodep;
  parr = ports + loarr;
  lat = pdep->rlat * 180/ M_PI;
  lon = pdep->rlon * 180/ M_PI;
  info(0,"nearest member hi at \ag%u 1 %u %f %f cnt %u %s",lodist,lodep,lat,lon,pdep->infconcnt,pdep->iname);
  lat = pdep->rlat * 180/ M_PI;
  lon = pdep->rlon * 180/ M_PI;
  info(0,"nearest member lo at \ag%u 1 %u %f %f cnt %u %s",lodist,loarr,lat,lon,parr->infconcnt,parr->iname);

  return 0;
}

#if 0
// check whether hop2 is to be filtered, given hop1, both being between the same port pairs
static int net0filter(lnet *net,ub4 hop1,ub4 hop2)
{
  struct chop *hp1,*hp2,*hp11,*hp21,*hops = net->chops;
  ub4 hopcnt = net->hopcnt;
  ub4 *choporg = net->choporg;
  ub4 hop11,hop12,hop21,hop22;

  hp1 = hops + hop1;
  hp2 = hops + hop2;
  if (hp1->kind != hp2->kind) return 0;
  ub4 lodur1 = hp1->lodur;
  ub4 lodur2 = hp2->lodur;

  if (lodur2 < lodur1 && lodur1 - lodur2 > 3) return 0;

  if (hop1 < hopcnt) hp11 = hp1;
  else {
    hop11 = choporg[hop1 * 2];
    hop12 = choporg[hop1 * 2 + 1];
    if (hops[hop11].evcnt < hops[hop12].evcnt) hp11 = hops + hop11;
    else hp11 = hops + hop12;
  }

  if (hop2 < hopcnt) hp21 = hp2;
  else {
    hop21 = choporg[hop2 * 2];
    hop22 = choporg[hop2 * 2 + 1];
    if (hops[hop21].evcnt < hops[hop22].evcnt) hp21 = hops + hop21;
    else hp21 = hops + hop22;
  }

  ub1 *covhrp1,*covhrp2,*covhr = net->covhr;
  ub8 rnghr = net->rnghr;
  ub8 mapofs1,mapofs2;
  ub4 h,cov1 = 0,cov2 = 0;

  mapofs1 = hp11->mapofshr;
  mapofs2 = hp21->mapofshr;
  covhrp1 = covhr + mapofs1;
  covhrp2 = covhr + mapofs2;

  for (h = 0; h < rnghr; h++) {
    if (covhrp1[h] && covhrp2[h]) continue;
    else if (covhrp1[h]) cov1++;
    else if (covhrp2[h]) cov2++;
  }
  if (cov2 == 0 && lodur2 > hp1->hidur && lodur2 - hp1->hidur >= 60 / max(hp11->avgperhr,1)) return 1;

  return 0;
}
#endif

// create coarse grid for quick distance and transfer estimate
static int mkgeogrid(struct network *net)
{
  struct port *pdep,*parr,*ports = net->ports;
  ub4 portcnt = net->portcnt;
  ub4 dep,arr;
  ub4 latscale = net->latscale;
  ub4 lonscale = net->lonscale;
  double RD = 180.0 / M_PI;

  ub4 minlat = hi32,minlon = hi32;
  ub4 maxlat = 0,maxlon = 0;
  ub4 cnt = 0;

  for (dep = 0; dep < portcnt; dep++) {

    pdep = ports + dep;
    if (pdep->valid == 0) continue;
    cnt++;
    minlat = min(minlat,pdep->lat);
    minlon = min(minlon,pdep->lon);
    maxlat = max(maxlat,pdep->lat);
    maxlon = max(maxlon,pdep->lon);
  }
  ub4 latrng = maxlat - minlat;
  ub4 lonrng = maxlon - minlon;

  if (latrng == 0) return error(0,"no lat range for %u",minlat);
  if (lonrng == 0) return error(0,"no lon range for %u",minlon);
  info(0,"lat range %f - %f",lat2rad(minlat,latscale) * RD,lat2rad(maxlat,latscale) * RD);
  info(0,"lon range %f - %f",lon2rad(minlon,lonscale) * RD,lon2rad(maxlon,lonscale) * RD);
  info(CC0,"%u ports skipped",portcnt - cnt);

  sassert(Geogrid < hi16,"Geogrid < 65536");

  ub4 gridscale = net->gridscale;
  ub4 geogrid = Geogrid * gridscale;
  if (geogrid >= hi16) {
    warn(0,"reducing %u * scale %u to %u",Geogrid,gridscale,hi16-1);
  }

  ub4 glatrng = min(latrng+1,geogrid);
  ub4 glonrng = min(lonrng+1,geogrid);
  ub4 gllrng = max(glatrng,glonrng) + 1;
  ub4 grng = (gllrng + 1) * (gllrng + 1);

  ub4 lat,lon;
  ub4 gridndx,gridndx2,gseqcnt,gseq = 0;
  ub8 glat,glon,glat2,glon2;

  info(Emp,"creating %u,%u cell distance grid from %u,%u, scale %u",glatrng,glonrng,latrng,lonrng,gridscale);

  ub4 gridseq,*gridseqs = talloc(grng,ub4,0xff,"net0 geogrid",glatrng);
  ub4 *gridndxs = talloc(grng,ub4,0,"net0 geogrid",glatrng);

  for (dep = 0; dep < portcnt; dep++) {

    pdep = ports + dep;
    if (pdep->valid == 0) continue;
    lat = pdep->lat;
    lon = pdep->lon;
    if (glatrng == latrng + 1) glat = lat;
    else glat = ((ub8)(lat - minlat) * glatrng) / (ub8)latrng;
    if (glonrng == lonrng + 1) glon = lon;
    else glon = ((ub8)(lon - minlon) * glonrng) / (ub8)lonrng;
    error_gt(glat,lat,dep);
    error_gt(glon,lon,dep);
    error_ovf(glat,ub2);
    error_ovf(glon,ub2);
    glat = min(glat,glatrng);
    glon = min(glon,glonrng);
    gridndx = (ub4)glat * gllrng + (ub4)glon;
    warncc(gridndx == 0,0,"port %u grid index 0 from %lu,%lu %s",dep,glat,glon,pdep->iname);
    error_ge(gridndx,grng);
    gridseq = gridseqs[gridndx];
    if (gridseq == hi32) {
      infocc(gseq < 100,0,"port %u seq %u for %f,%f",dep,gseq,pdep->rlat * RD,pdep->rlon * RD);
      gridseq = gridseqs[gridndx] = gseq++;
      gridndxs[gridseq] = gridndx;
    }
    pdep->gridseq = gridseq;
//    pdep->gridndx = gridndx;
    pdep->gridlat = (ub4)glat;
    pdep->gridlon = (ub4)glon;
  }
  error_z(gseq,latrng);

  gseqcnt = gseq;
  info(Emp,"\ah%u geo grid cells",gseqcnt);

  for (dep = 0; dep < portcnt; dep++) {
    pdep = ports + dep;
    gridseq = pdep->gridseq;
    error_ge_cc(gridseq,gseqcnt,"port %u %u",dep,pdep->valid);
  }

  // apply sequences
  ub8 gseq12,gseqx,gseq2 = (ub8)gseqcnt * gseqcnt;
  ub2 *seqdist = alloc(gseq2,ub2,0,"net0 geodist",gseq);
  ub1 *seqlotx = alloc(gseq2,ub1,0,"net0 geolotx",gseq);

  struct eta eta;
  double dist;
  ub4 idist;
  double rlat,rlon,rlat2,rlon2;
  ub4 lat2,lon2;
  ub4 seq1,seq2;
  gseqx = 0;

  for (seq1 = 0; seq1 < gseqcnt; seq1++) {

    if (progress(&eta,"filling grid cell %u of %u  \ah%lu",seq1,gseqcnt,gseqx)) return 1;

    gridndx = gridndxs[seq1];

    glat = gridndx / gllrng;
    glon = gridndx % gllrng;
    lat = (ub4)((glat * latrng) / (ub8)glatrng) + minlat;
    lon = (ub4)((glon * lonrng) / (ub8)glonrng) + minlon;
    rlat = lat2rad(lat,latscale);
    rlon = lon2rad(lon,lonscale);

    for (seq2 = 0; seq2 < gseqcnt; seq2++) {
      if (seq1 == seq2) continue;

      gridndx2 = gridndxs[seq2];

      glat2 = gridndx2 / gllrng;
      glon2 = gridndx2 % gllrng;
      lat2 = (ub4)((glat2 * latrng) / (ub8)glatrng) + minlat;
      lon2 = (ub4)((glon2 * lonrng) / (ub8)glonrng) + minlon;
      rlat2 = lat2rad(lat2,latscale);
      rlon2 = lon2rad(lon2,lonscale);

      dist = geodist(rlat,rlon,rlat2,rlon2,"grid");
      idist = (ub4)(dist + 0.5);
      gseq12 = (ub8)seq1 * gseqcnt + seq2;
      error_ge(gseq12,gseq2);
      warncc(seqdist[gseq12] != 0,Iter,"seq %u-%u grid %u-%u dist %u",seq1,seq2,gridndx,gridndx2,idist);
      seqdist[gseq12] = (ub2)(idist >> Gridshift);
      // info(Iter,"seq %u-%u grid %u-%u dist %u",seq1,seq2,gridndx,gridndx2,idist);
      gseqx++;
    }

  }
  net->seqdist = seqdist;
  net->seqlotx = seqlotx;
  net->seqdlen = gseqcnt;

  afree(gridseqs,"net0 geogrid");
  afree(gridndxs,"net0 geogrid");

  for (dep = 0; portcnt < 50000 && dep < portcnt; dep++) {
    if (progress0(&eta,"check grid port %u of %u",dep,portcnt)) return 1;

    pdep = ports + dep;
    if (pdep->valid == 0) continue;
    seq1 = pdep->gridseq;
    error_ge(seq1,gseqcnt);
    rlat = pdep->rlat;
    rlon = pdep->rlon;
    for (arr = 0; arr < portcnt; arr++) {
      if (dep == arr) continue;
      parr = ports + arr;
      if (parr->valid == 0) continue;
      if (pdep->gridlat + 1 >= parr->gridlat && pdep->gridlon + 1 >= parr->gridlon
    && parr->gridlat + 1 >= pdep->gridlat && parr->gridlon + 1 >= pdep->gridlon ) continue;

      seq2 = parr->gridseq;
      error_ge(seq2,gseqcnt);
      rlat2 = parr->rlat;
      rlon2 = parr->rlon;
      dist = geodist(rlat,rlon,rlat2,rlon2,"grid");
      idist = (ub4)seqdist[(ub8)seq1 * gseqcnt + seq2] << Gridshift;
      infocc(dep < 5 && arr < 5,0,"port %u-%u seq %u,%u grid %u,%u-%u,%u dist %u / %u",dep,arr,seq1,seq2,pdep->gridlat,pdep->gridlon,parr->gridlat,parr->gridlon,(ub4)(dist + 0.5),idist);

      if (dist > 200 && (dist * 2 < idist || idist * 2 < dist)) {
        warn(0,"port %u-%u seq %u,%u grid %u,%u-%u,%u dist %u / %u %f,%f - %f,%f",dep,arr,seq1,seq2,pdep->gridlat,pdep->gridlon,parr->gridlat,parr->gridlon,(ub4)(dist + 0.5),idist,rlat * RD,rlon * RD,rlat2 * RD,rlon2 * RD);
      }
    }
  }

  return 0;
}

#if 0
static ub4 geogdist(struct network *net,struct port *pdep,struct port *parr)
{
  ub4 seq1 = pdep->gridseq;
  ub4 seq2 = parr->gridseq;
  ub4 gseqcnt = net->seqdlen;
  ub2 *seqdist = net->seqdist;

  ub4 dist = (ub4)seqdist[(ub8)seq1 * gseqcnt + seq2] << Gridshift;
  if (dist < Gridlim) dist = fgeodist(pdep,parr,1);

  return dist;
}
#endif

static int mkportreach(struct network *net)
{
  ub4 hop,chopcnt = net->chopcnt;
  ub4 dep,portcnt = net->portcnt;
  struct port *pdep,*parr,*ports = net->ports;
  struct chop *hp,*hops = net->chops;
  ub4 dist;
  ub8 sumreach;

  info0(0,"make port reach");
  for (hop = 0; hop < chopcnt; hop++) {
    hp = hops + hop;
    pdep = ports + hp->dep;
    parr = ports + hp->arr;
    dist = fgeodist(pdep,parr,1);
    pdep->sumreach += dist;
  }
  for (dep = 0; dep < portcnt; dep++) {
    pdep = ports + dep;
    sumreach = pdep->sumreach;
    pdep->msbreach = msb(sumreach);
  }
  info0(0,"done making port reach");
  return 0;
}

// not yet used
static int mkxfers(struct network *net)
{
  ub4 x,xfercnt = net->xfercnt;
  ub4 portcnt = net->portcnt;
  struct xfer *xp,*xfers = net->xfers;
  ub4 nox = 0;
  iadrbase *noxfer = &net->noxfer;
  ub4 dep,arr;

  if (xfercnt == 0) return info0(0,"skip init for no xfers");

  mkiadr0(noxfer,portcnt,portcnt,ub2,10000,10,"net noxfer");

  for (x = 0; x < xfercnt; x++) {
    xp = xfers + x;
    dep = xp->fromport;
    arr = xp->toport;
    switch(xp->type) {
    case 0: break;
    case 1: break;
    case 2: break;
    case 3: nox++; iadrinc(noxfer,dep,arr,0); break;
    }
  }
  mkiadr1(noxfer);

  for (x = 0; x < xfercnt; x++) {
    xp = xfers + x;
    dep = xp->fromport;
    arr = xp->toport;
    switch(xp->type) {
    case 0: break;
    case 1: break;
    case 2: break;
    case 3: nox++; wriadr2(noxfer,dep,arr,1); break;
    }
  }
  finiadr(noxfer);
  return 0;
}

#define Net0lim 2048

// create 0-stop connectivity matrix and derived info.
// n-stop builds on this
// todo:
// maintain top-n for each of duration, coverage and frequency
// select n best from these 3 sets
// add best <dur,cov,frq> score per deparr
// use this to filter net1

todo foreach hop
       add hp->arr to hp->dep conlst directly, tentative list
     foreach port
       sort unique conlst and trim

static int mknet0(struct network *net)
{
  ub4 portcnt = net->portcnt;
  ub4 hopcnt = net->hopcnt;
  ub4 chopcnt = net->chopcnt;
  ub4 thopcnt = net->thopcnt;
  ub4 whopcnt = net->whopcnt;
  ub4 ridcnt = net->ridcnt;

  struct port *ports,*pdep,*parr;
  struct chop *chp,*chp2,*chops = net->chops;
  struct route *rp,*rp2,*routes = net->routes;
  char *dname,*aname;
  ub4 *portsbyhop;
  ub2 concnt,cnt,cntlim,gen;
  ub4 ofs,lstlen;
  iadrbase *cnts = net->concnt;
  iadrbase *precnts = &net->conipos;
  iadrbase *conofs = net->conofs;
  ub4 walklimit = net->walklimit;
  ub4 n1walklimit = net->net1walklimit;
  ub4 hop,*con0lst;
  ub4 *hopdist;
  ub4 dep,arr,dep1,arr1,depcnt,arrcnt;
  ub4 rid;
  ub4 needconn,haveconn;
  ub2 iv;
  const char *rname;

  if (portcnt == 0) return error(0,"no ports for %u hops net",hopcnt);
  if (hopcnt == 0) return error(0,"no hops for %u port net",portcnt);
  error_lt(chopcnt,hopcnt);

  cntlim = (ub2)globs.dirconlimit;
  if (cntlim > Net0lim) { warn(0,"0-stop limit from %u to %u vars",cntlim,Net0lim); cntlim = Net0lim; }
  else info(0,"0-stop limit %u vars",cntlim);
  info(0,"init 0-stop connections for %u port %u hop network",portcnt,hopcnt);

  ports = net->ports;

  portsbyhop = net->portsbyhop;

  ub4 sparsethres = net->sparsethres;

  clear(precnts);
  if (mkiadr0(cnts,portcnt,portcnt,ub2,sparsethres * 2,8,"net0 cnts")) return 1;
  if (mkiadr0(precnts,portcnt,portcnt,ub2,sparsethres * 2,8,"net0 pos")) return 1;
  if (mkiadr0(conofs,portcnt,portcnt,ub8,sparsethres,16,"net0 ofss")) return 1;
  if (mkiadrmap(precnts,"net0 cntmap")) return 1;

  con0lst = mkblock(net->conlst,whopcnt,ub4,Init1,"net0 0-stop conlst");

  ub1 mode,*modes = alloc(whopcnt,ub1,0,"net0 modes",whopcnt);

  hopdist = net->hopdist;

  ub4 nhopcnt = 0,noevcnt = 0,ev1cnt = 0,noportcnt = 0;

  struct eta eta;

  ub4 lodur,*lodurs = alloc(whopcnt,ub4,0xff,"net lodur",whopcnt);

  // create 0-stop connectivity
  // preliminary counts
  for (hop = 0; hop < whopcnt; hop++) {
    if (progress(&eta,"hop %u of %u 0-stop net pass 1  \ah%u conns",hop,whopcnt,nhopcnt)) return 1;

    chp = chops + hop;
    dep = chp->dep;
    arr = chp->arr;
    error_eq(dep,arr);

    error_ge(dep,portcnt);
    error_ge(arr,portcnt);

    pdep = ports + dep;
    parr = ports + arr;
    if (pdep->valid == 0 || parr->valid == 0) { noportcnt++; continue; }

    lodurs[hop] = chp->lodur;

    rid = chp->rid;
    error_eq(rid,hi32);
    error_ge(rid,ridcnt);
    if (hop < chopcnt) {
      if (chp->evcnt == 0) { info(Iter,"%c%chop %u rid %u no evs",chp->ctype,chp->ckind,hop,rid); noevcnt++; continue; }
      if (chp->kind != Taxi && chp->evcnt < 2) { info(Iter,"hop %u 1 ev %s %s",hop,pdep->iname,parr->name); ev1cnt++; continue; }
    }
    iadrinc(precnts,dep,arr,0);

    nhopcnt++;
  }
  warncc(nhopcnt != whopcnt,0,"marked %u out of %u hops, skipped %u",nhopcnt,whopcnt,whopcnt - nhopcnt);
  warn(CC0,"%u hops without events",noevcnt);
  info(CC0,"%u hops with 1 event",ev1cnt);
  warn(CC0,"%u port\as invalid",noportcnt);

  ub8 conperc = (100UL * precnts->inicnt) / ((ub8)portcnt * portcnt);

  info(Emp,"\ah%u tentative pairs %lu%%",precnts->inicnt,conperc);

  mkiadr1(precnts);
  cpiadr(cnts,precnts);
  mkiadr1(cnts);

  // initial assignments
  ub4 ovfcnt = 0,hicon = 0,hidep = 0,hiarr = 0;
  for (hop = 0; hop < whopcnt; hop++) {
    if (progress(&eta,"hop \ah%u of \ah%u 0-stop net pass 2  \ah%u conns",hop,whopcnt,nhopcnt)) return 1;
    dep = portsbyhop[hop * 2];
    arr = portsbyhop[hop * 2 + 1];
    if (dep == hi32 || arr == hi32 || dep == arr) continue;

    pdep = ports + dep;
    parr = ports + arr;
    if (pdep->valid == 0 || parr->valid == 0) continue;

    chp = chops + hop;
    if (hop < chopcnt) {
      if (chp->evcnt == 0) continue;
      if (chp->kind != Taxi && chp->evcnt < 2) continue;
    }

    dname = pdep->iname;
    aname = parr->iname;

    concnt = rdiadr2(precnts,dep,arr);

    if (concnt >= cntlim) {
      ovfcnt++;
      continue;
    } else if (concnt == cntlim-1) {
      info(0,"exceeding %u hops at %u port %u-%u %s to %s",concnt,hop,dep,arr,dname,aname);
      ovfcnt++;
    } else if (concnt == 0) iadrinc(conofs,dep,arr,0);

    if (wriadr2(precnts,dep,arr,(ub2)(concnt + 1))) return errorfln(FLN,0,precnts->fln,"hop %u",hop);

    if (hop >= thopcnt) {
      pdep->modes |= Walkbit;
      parr->modes |= Walkbit;
    } else if (hop >= chopcnt) {
      pdep->modes |= Taxibit;
      parr->modes |= Taxibit;
    }
    chp->net0 = 1;
    if (concnt > hicon) { hicon = concnt; hidep = dep; hiarr = arr; }
  }
  warn(CC0,"limiting 0-stop net by \ah%u",ovfcnt);

  finiadr(precnts);

  mkiadr1(conofs);

  // show highest conn
  pdep = ports + hidep; parr = ports + hiarr;
  info(Emp,"highest conn %u between ports %u-%u %s to %s",hicon,hidep,hiarr,pdep->name,parr->name);

  for (hop = 0; hop < whopcnt; hop++) {
    dep = portsbyhop[hop * 2];
    arr = portsbyhop[hop * 2 + 1];
    if (dep == hi32 || arr == hi32 || dep == arr) continue;
    if (dep != hidep || arr != hiarr) continue;

    rid = hi32;
    if (hop < chopcnt) {
      chp = chops + hop;
      rid = chp->rid;
      error_ge(rid,ridcnt);
      rname = routes[rid].name;
    } else if (hop < thopcnt) rname = "taxi";
    else rname = "walk";

    if (hop < hopcnt) {
      info(Notty,"  hop %u rid %u route %s",hop,rid,rname);
    } else if (hop < chopcnt) {
      chp = chops + hop;
      info(Notty,"  chop %u = %u-%u rid %u route %s",hop,chp->hop1,chp->hop2,rid,rname);
    } else info(Notty," whop %u dist %u",hop,hopdist[hop]);
  }

  ofs = 0;
  needconn = haveconn = 0;

  // assign offsets
  for (dep = 0; dep < portcnt; dep++) {

    if (progress(&eta,"port %u of %u 0-stop net \ah%u conns",dep,portcnt,ofs)) return 1;

    pdep = ports + dep;
    if (pdep->valid == 0) continue;

    for (arr = 0; arr < portcnt; arr++) {
      if (dep == arr) continue;
      parr = ports + arr;
      if (parr->valid == 0) continue;

      needconn++;

      concnt = rdiadr2(precnts,dep,arr);
      if (concnt == 0) continue;

      if (wriadr8(conofs,dep,arr,ofs)) return 1;
      ofs += concnt;
    }
  }
  finiadr(conofs);
  lstlen = ofs;

  error_gt(ofs,whopcnt,0);

  info(Emp,"0-stop net \ah%u triplets",ofs);

  net->lstlen[0] = lstlen;

  ub1 *hopmodes = net->hopmodes = alloc(whopcnt,ub1,0,"net0 modes",whopcnt);
  enum txkind kind;
  ub4 prv,duphops = 0,dupchops = 0,dupwhops = 0,flthops = 0;
  ub4 pairs = 0,triplets = 0;
  ub4 prvhop;

  // pass 3: fill
  info(0,"pass 3 0-stop %u hop net",hopcnt);
  for (hop = 0; hop < whopcnt; hop++) {

    if (progress(&eta,"hop %u of %u 0-stop net pass 3  \ah%u conns",hop,whopcnt,nhopcnt)) return 1;

    chp = chops + hop;
    kind = chp->kind;

    if (hop < chopcnt) {
      rid = chp->rid;
      error_z(kind,0);
      rp = routes + rid;
    } else {
      rp = NULL;
    }

    mode = 0;
    switch(kind) {
    case Unknown: case Kindcnt: break;
    case Airint: case Airdom: mode = Airbit; break;
    case Rail: mode = Railbit; break;
    case Bus: mode = Busbit; break;
    case Ferry: mode = Ferrybit; break;
    case Taxi: mode = Taxibit; break;
    case Walk: mode = Walkbit; break;
    }
    hopmodes[hop] = mode;
    errorcc(mode == 0,0,"hop %u kind %u",hop,kind);
    error_z(mode,hop);

    if (hop < chopcnt) {
      if (chp->evcnt == 0) continue;
      if (chp->kind != Taxi && chp->evcnt < 2) continue;
    }

    dep = portsbyhop[hop * 2];
    arr = portsbyhop[hop * 2 + 1];
    if (dep == hi32 || arr == hi32 || dep == arr) continue;
    pdep = ports + dep;
    parr = ports + arr;
    if (pdep->valid == 0 || parr->valid == 0) continue;

    gen = rdiadr2(cnts,dep,arr);
    cnt = rdiadr2(precnts,dep,arr);

    if (gen == cntlim) continue;

    error_ge(gen,cnt);
    ofs = (ub4)rdiadr8(conofs,dep,arr);
    error_ge(ofs+gen,whopcnt);
    for (prv = 0; gen && prv < gen; prv++) {
      prvhop = con0lst[ofs+prv];
      if (hop >= thopcnt && prvhop >= thopcnt) {
        warn(Ret1,"duplicate walk link %u-%u",dep,arr);
        dupwhops++;
        break;
      } else if (hop >= chopcnt || prvhop >= chopcnt) continue;
//      if (net0filter(net,prvhop,hop)) { flthops++; break; }
      else if (hop < hopcnt && prvhop < hopcnt && dupevs(net,prvhop,hop)) { // todo move to netbase
        chp2 = chops + prvhop;
        rp2 = chp2->rid == hi32 ? NULL : routes + chp2->rid;
        if (hop < hopcnt) {
          infocc(duphops < 50,0,"dup hop %u %s %s to %s",hop,rp ? rp->name : "",rp2 ? rp2->name : "",pdep->iname);
          duphops++;
        } else if (hop < chopcnt) {
          infocc(dupchops < 50,0,"dup hop %u %s %s to %s",hop,rp ? rp->name : "",rp2 ? rp2->name : "",pdep->iname);
          dupchops++;
        }
        break;
      }
    }
    if (gen && prv < gen) continue;
    con0lst[ofs+gen] = hop;
    modes[ofs+gen] = mode;
    if (gen == 0) pairs++;
    triplets++;
    if (wriadr2(cnts,dep,arr,(ub2)(gen + 1))) return 1;
  }

  ub8 port2 = (ub8)portcnt * portcnt;
  info(Emp,"0-stop net \ah%u triplets in \ah%u pairs \ap%lu%lu",triplets,pairs,(ub8)pairs,port2);

  rmiadr(precnts);
  finiadr(cnts);

  info(CC0,"\ah%u of \ah%u duplicate hops",duphops,hopcnt);
  info(CC0,"\ah%u of \ah%u duplicate chops",dupchops,chopcnt - hopcnt);
  info(CC0,"\ah%u of \ah%u duplicate whops",dupwhops,whopcnt - chopcnt);
  info(CC0,"%u filtered hops",flthops);

  net->pairs[0] = pairs;

  net->modes[0] = modes;

  // sort on duration
  ub4 tmplst[2048];
  ub8 dursort[2048];
  ub4 *lst;
  ub4 v1,idx;
  int dosort = dorun(FLN,Runnetn,1);

  for (dep = 0; dep < portcnt && dosort; dep++) {
    if (progress0(&eta,"sorting port %u of %u 0-stop net",dep,portcnt)) return 1;
    pdep = ports + dep;
    if (pdep->valid == 0) continue;
    for (arr = 0; arr < portcnt; arr++) {
      if (dep == arr) continue;
      parr = ports + arr;
      if (parr->valid == 0) continue;
      cnt = rdiadr2(cnts,dep,arr);
      if (cnt == 0) continue;
      haveconn++;
      ofs = (ub4)rdiadr8(conofs,dep,arr);
      lst = con0lst + ofs;
      error_ge(cnt,Elemcnt(tmplst));
      hop = lst[0];
      error_ge(hop,whopcnt);
      mode = modes[ofs];
      error_z(mode,ofs);
      if (cnt == 1) continue;

      memcpy(tmplst,lst,cnt * sizeof(ub4));
      for (v1 = 0; v1 < cnt; v1++) {
        hop = lst[v1];
        error_ge(hop,whopcnt);
        lodur = lodurs[hop];
        dursort[v1] = (ub8)lodur << 32 | v1;
      }
      sort8(dursort,cnt,FLN,"net0");
      for (v1 = 0; v1 < cnt; v1++) {
        idx = dursort[v1] & hi32;
        error_ge(idx,cnt);
        hop = tmplst[idx];
        error_ge(hop,whopcnt);
        mode = hopmodes[hop];
        error_z(mode,hop);
        lst[v1] = hop;
        modes[ofs+v1] = mode;
      }
    }
  }
  infocc(haveconn,Emp,"  0-stop connectivity \ah%3u of \ah%3u  = \ap%lu%lu",haveconn,needconn,(ub8)haveconn,(ub8)needconn);

  for (dep = 0; dep < portcnt && portcnt < 40000; dep++) {
    if (progress0(&eta,"verify dep %u of %u",dep,portcnt)) return 1;
    for (arr = 0; arr < portcnt; arr++) {
      cnt = rdiadr2(cnts,dep,arr);
      if (cnt == 0) continue;
      ofs = (ub4)rdiadr8(conofs,dep,arr);
      lst = con0lst + ofs;
      for (v1 = 0; v1 < cnt; v1++) {
        hop = lst[v1];
        error_ge(hop,whopcnt);
        dep1 = portsbyhop[hop * 2];
        arr1 = portsbyhop[hop * 2 + 1];
        error_ne(dep1,dep);
        error_ne(arr1,arr);
      }
    }
  }
  net->needconn = needconn;

  int doconchk = globs.engvars[Eng_conchk];

  if (dosort == 0 && doconchk == 0) return 0;

  // get connectivity stats
  bool doconstat = (portcnt < 20000);
  ub4 hicnt = 0,hiport = 0;
  ub4 depstats[32];
  ub4 arrstats[32];
  ub4 depivs = Elemcnt(depstats) - 1;
  ub4 arrivs = Elemcnt(arrstats) - 1;

  aclear(arrstats);
  aclear(depstats);

  // prepare sorted outbounds and inbounds per port for search
  ub4 *deplst = alloc(pairs,ub4,0,"net0 deplst",0);
  ub4 *arrlst = alloc(pairs,ub4,0,"net0 arrlst",0);
  ub4 *depdurlst = alloc(pairs,ub4,0,"net0 depdurlst",0);
  ub4 *arrdurlst = alloc(pairs,ub4,0,"net0 arrdurlst",0);

  ub4 *portdst = talloc(portcnt, ub4,0,"net0 portdst",portcnt);

  ub8 *dasort = talloc(portcnt,ub8,0,"net0 depsort",0);

  ub4 ddep,darr,dvia;
  ub4 daofs = 0,vaofs,viacnt,cumviacnt = 0;
  ub4 via;

  for (dep = 0; dep < portcnt; dep++) {
    if (progress0(&eta,"dep conlst port %u of %u",dep,portcnt)) return 1;
    pdep = ports + dep;
    if (pdep->valid == 0) continue;
    pdep->depofs[0] = daofs;
    depcnt = 0;
    for (arr = 0; arr < portcnt; arr++) {
      if (dep == arr) continue;
      parr = ports + arr;
      if (parr->valid == 0) continue;
      cnt = rdiadr2(cnts,dep,arr);
      if (cnt == 0) continue;
      ofs = (ub4)rdiadr8(conofs,dep,arr);
      hop = con0lst[ofs];
      lodur = lodurs[hop];   // sorted above on dur, first entry only
      dasort[depcnt] = ((ub8)lodur << 32) | (ub8)arr;
      depcnt++;
      if (depcnt > hicnt) { hicnt = depcnt; hiport = dep; }
    }
    if (depcnt > 1) sort8(dasort,depcnt,FLN,"net 0 deplst");
    else if (depcnt == 0) continue;
    error_gt(daofs + depcnt,pairs,depcnt);
    for (darr = 0; darr < depcnt; darr++) {
      arr = dasort[darr] & hi32;
      lodur = (ub4)(dasort[darr] >> 32);
      deplst[daofs+darr] = arr;
      depdurlst[daofs+darr] = lodur;
    }
    error_ge((ub8)daofs + depcnt,hi32);
    daofs += depcnt;

    pdep->depcnt[0] = depcnt;
    portdst[dep] = depcnt;
    depstats[min(depivs,depcnt)]++;
  }
  error_ne(daofs,pairs);
  for (iv = 0; iv <= depivs; iv++) {
    infocc(depstats[iv],0,"%u port\as reaches %u port\as", depstats[iv],iv);
  }
  pdep = ports + hiport;
  infocc(doconstat,0,"port %u is reached by %u ports %s",hiport,hicnt,pdep->name);

  ub1 *arrmap = talloc0(portcnt,ub1,0);

  // prepare dep via list
  todo not use, as net1 on net0 is ok

  for (dep = 0; dep < portcnt; dep++) {
    if (progress0(&eta,"dep vialst port %u of %u",dep,portcnt)) return 1;
    pdep = ports + dep;
    if (pdep->valid == 0) continue;
    daofs = pdep->depofs[0];
    depcnt = pdep->depcnt[0];
    nclear(arrmap,portcnt);
    arrmap[dep] = 1;
    for (darr = 0; darr < depcnt; darr++) {
      arr = deplst[daofs + darr] & Nbrmask;
      cnt = rdiadr2(cnts,dep,arr);
      error_z(cnt,dep);
      arrmap[arr] = 1;
    }
    viacnt = 0;
    for (darr = 0; darr < depcnt; darr++) {
      arr = deplst[daofs + darr] & Nbrmask;
      parr = ports + arr;
      if (pdep->tripend && parr->tripstart) deplst[daofs + darr] = arr | Trip0bit;  not used
      vaofs = parr->depofs[0];
      arrcnt = parr->depcnt[0];
      for (dvia = 0; dvia < arrcnt; dvia++) {
        via = deplst[vaofs + dvia] & Nbrmask;
        error_ge(via,portcnt);
        if (arrmap[via] == 0) break;
      }
      if (dvia == arrcnt) continue; // can not be a via
      deplst[daofs + darr] |= Viabit;
      viacnt++;
    }
    pdep->viacnt[0] = viacnt;
    cumviacnt += viacnt;
  }
  info(0,"\ah%u vias",cumviacnt);
  if (cumviacnt == 0) return error0(0,"no vias");

  daofs = 0;
  hicnt = hiport = 0;
  for (arr = 0; arr < portcnt; arr++) {
    if (progress0(&eta,"arr conn port %u of %u",arr,portcnt)) return 1;
    parr = ports + arr;
    if (parr->valid == 0) continue;
    parr->arrofs[0] = daofs;
    arrcnt = 0;
    for (dep = 0; dep < portcnt; dep++) {
      if (dep == arr) continue;
      pdep = ports + dep;
      if (pdep->valid == 0) continue;
      cnt = rdiadr2(cnts,dep,arr);
      if (cnt == 0) continue;
      ofs = (ub4)rdiadr8(conofs,dep,arr);
      hop = con0lst[ofs];
      lodur = lodurs[hop];   // sorted above on dur, first entry only
      dasort[arrcnt] = ((ub8)lodur << 32) | (ub8)dep;

      arrcnt++;
      if (arrcnt > hicnt) { hicnt = arrcnt; hiport = arr; }
    }
    if (arrcnt > 1) sort8(dasort,arrcnt,FLN,"net 0 arrlst");
    else if (arrcnt == 0) continue;
    error_gt(daofs + arrcnt,pairs,arrcnt);
    for (ddep = 0; ddep < arrcnt; ddep++) {
      dep = (ub4)(dasort[ddep] & hi32);
      lodur = (ub4)(dasort[ddep] >> 32);
      arrlst[daofs+ddep] = dep;
      arrdurlst[daofs+ddep] = lodur;
    }
    daofs += arrcnt;

    parr->arrcnt[0] = arrcnt;
    arrstats[min(arrivs,arrcnt)]++;
  }
  error_ne(daofs,pairs);

  // prepare arr via list
  cumviacnt = 0;
  for (arr = 0; arr < portcnt; arr++) {
    if (progress0(&eta,"arr conn port %u of %u",arr,portcnt)) return 1;
    parr = ports + arr;
    if (parr->valid == 0) continue;
    daofs = parr->arrofs[0];
    arrcnt = parr->arrcnt[0];
    nclear(arrmap,portcnt);
    arrmap[arr] = 1;
    for (ddep = 0; ddep < arrcnt; ddep++) {
      dep = arrlst[daofs + ddep] & Nbrmask;
      arrmap[dep] = 1;
    }
    viacnt = 0;
    for (ddep = 0; ddep < arrcnt; ddep++) {
      dep = arrlst[daofs + ddep] & Nbrmask;
      pdep = ports + dep;
      if (pdep->tripend && parr->tripstart) arrlst[daofs + ddep] = dep | Trip0bit;
      vaofs = pdep->arrofs[0];
      depcnt = pdep->arrcnt[0];
      for (dvia = 0; dvia < depcnt; dvia++) {
        via = arrlst[vaofs + dvia] & Nbrmask;
        error_ge(via,portcnt);
        if (arrmap[via] == 0) break;
      }
      if (dvia == depcnt) continue; // can not be a via
      arrlst[daofs + ddep] |= Viabit;
      viacnt++;
    }
    parr->viacnt[0] = viacnt;
    cumviacnt += viacnt;
  }
  info(0,"\ah%u arr vias",cumviacnt);
  if (cumviacnt == 0) return error0(0,"no vias");

  for (iv = 0; iv <= arrivs; iv++) {
    infocc(arrstats[iv],0,"%u port\as reached by %u port\as", arrstats[iv],iv);
  }
  parr = ports + hiport;
  infocc(doconstat,0,"port %u reached by %u ports %s",hiport,hicnt,parr->name);

  afree0(arrmap);

  net->deplst[0] = deplst;
  net->arrlst[0] = arrlst;
  net->depdurlst[0] = depdurlst;
  net->arrdurlst[0] = arrdurlst;
  net->portdst[0] = portdst;

  return 0;
}

// create n-stop connectivity matrix and derived info
static int mk_netn(struct network *net,ub4 nstop,ub4 netstop)
{
  ub4 portcnt = net->portcnt;
  ub4 hopcnt = net->hopcnt;
  ub4 whopcnt = net->whopcnt;
  struct port *ports,*pdep,*parr;
  block *lstblk;
  iadrbase *concnt,*conofs;
  ub4 *lst;
  ub4 ofs;
  ub4 dep,arr,deparr;
  ub4 nstop1,cnt,nleg;
  int rv;

  // only fill n-stop if under given nstop-1
  ub4 cntonly;

  // max #variants per [dep,arr]
  ub4 var12limit;
  ub4 varlimit1 = globs.net1limit[2];
  ub4 varlimit2 = globs.net2limit[2];
  ub4 varlimit3 = globs.net3limit[2];
  ub4 altlimit3 = globs.net3altlim;

  error_z(nstop,0);
  error_ge(nstop,Nstop);
  error_gt(nstop,Netn,netstop);
  error_gt(netstop,Netn,nstop);

  error_zz(portcnt,hopcnt);

  vrb0(0,"init %u-stop connections for %u port %u hop network",nstop,portcnt,whopcnt);

  // todo configurable
  switch (nstop) {
  case 1: cntonly = 256; var12limit = hi24; break;
  case 2: cntonly = 256; var12limit = hi24; break;
  case 3: cntonly = 256; var12limit = hi24; break;
  default: return 1;
  }

  if (cntonly == 0 && nstop && net->needconn <= net->haveconn[nstop-1]) {
    return info(0,"skip %u-stop init on %u-stop coverage complete",nstop,nstop-1);
  }

  switch(nstop) {
  case 1: rv = mknet1(net,varlimit1,var12limit,cntonly,netstop);
          if (rv) return rv;
          break;
  case 2: rv = mknet2(net,varlimit2,var12limit,cntonly,netstop);
          if (rv) return rv;
          break;
#if 0
  case 3: rv = mknet3(net,varlimit3,var12limit,altlimit3,cntonly,netstop);
          if (rv) warn(0,"net3 returned %d",rv);
          break;
#endif
  default: return error(0,"%u-stop net not supported",nstop);
  }

  if (net->lstlen[nstop] == 0) return 0;

  ports = net->ports;

  // get connectivity stats
  if (portcnt > 40000) return 0;

  unsigned long doneconn,doneperc,leftcnt,needconn = net->needconn;
  ub4 n,da,nda = 0,port,hascon,hicon,arrcon,loarrcon,lodep = 0;
  ub4 tports[Nstop];
  ub4 deparrs[16];
  ub4 nstops[16];
  ub4 lodeparrs[16];
  ub4 lonstops[16];
  ub4 ndacnt = Elemcnt(deparrs);
  struct port *pp;
  struct eta eta;

  for (nda = 0; nda < ndacnt; nda++) {
    deparrs[nda] = lodeparrs[nda] = hi32;
    nstops[nda] = lonstops[nda] = 0;
  }

  doneconn = 0;
  loarrcon = hi32;

  for (dep = 0; dep < portcnt; dep++) {
    if (progress0(&eta,"get connectivity port %u of %u",dep,portcnt)) return 1;
    arrcon = 0;
    nda = 1;
    pdep = ports + dep;
    if (pdep->valid == 0) continue;

    for (arr = 0; arr < portcnt; arr++) {
      if (dep == arr) continue;
      deparr = dep * portcnt + arr;
      hascon = 0;
      nstop1 = 0;
      while (nstop1 <= nstop) {
        if (net->lstlen[nstop1] == 0) { nstop1++; continue; }
        concnt = net->concnt + nstop1;
        error_z(concnt->state,nstop1);
        if (rdiadr2(concnt,dep,arr)) { hascon = 1; break; }
        nstop1++;
      }
      if (hascon) {
        arrcon++;
        if (nstop1 >= nstops[0]) { nstops[0] = nstop1; deparrs[0] = deparr; }
      } else {
        if (nda < ndacnt) deparrs[nda++] = deparr;
      }
    }
    doneconn += arrcon;
    if (arrcon < loarrcon) {
      loarrcon = arrcon;
      lodep = dep;
      memcpy(lodeparrs,deparrs,ndacnt * sizeof(ub4));
      memcpy(lonstops,nstops,ndacnt * sizeof(ub4));
    }
    leftcnt = portcnt - arrcon - 1;
    if (leftcnt) {
      infovrb(nstop > 2 || portcnt < 5000,Iter,"port %u lacks %u of %u connection\as %s",dep,(ub4)leftcnt,portcnt - 1,pdep->name);
      for (da = 1; da < nda; da++) {
        deparr = deparrs[da];
        if (deparr == hi32) break;
        arr = deparr % portcnt;
        parr = ports + arr;
        infovrb(nstop > 3,Notty,"port %u %s no %u-stop connection to %u %s",dep,pdep->name,nstop,arr,parr->name);
      }
    }
  }
  net->haveconn[nstop] = doneconn;
  if (needconn) {
    error_gt(doneconn,needconn,0);
    doneperc = doneconn * 100 / needconn;
    if (doneperc > 98) info(0,"0-%u-stop connectivity \ah%3lu of \ah%3lu = %02u%%, left %lu", nstop,doneconn,needconn,(ub4)doneperc,needconn - doneconn);
    else info(0,"0-%u-stop connectivity \ah%3lu of \ah%3lu = %02u%%", nstop,doneconn,needconn,(ub4)doneperc);
  } else info(0,"0-%u-stop connectivity \ah%3lu", nstop,doneconn);

  pdep = ports + lodep;
  leftcnt = portcnt - loarrcon - 1;
  if (leftcnt) info(0,"port %u lacks %u of %u connection\as %s",lodep,(ub4)leftcnt,portcnt - 1,pdep->name);

  for (nda = 0; nda < ndacnt; nda++) {
    deparr = lodeparrs[nda];
    if (deparr == hi32) break;
    hicon = lonstops[nda];
    dep = deparr / portcnt;
    arr = deparr % portcnt;
    pdep = ports + dep;
    parr = ports + arr;
    concnt = net->concnt + hicon;
    if (concnt->state == 0) return error(0,"%u stops cnt nil",hicon);
    cnt = rdiadr2(concnt,dep,arr);
    info(V0,"%u-%u %u vars at %u stops %s to %s",dep,arr,cnt,hicon,pdep->name,parr->name);
    if (cnt == 0) continue;
    nleg = hicon + 1;
    conofs = net->conofs + hicon;
    ofs = (ub4)rdiadr8(conofs,dep,arr);
    lstblk = net->conlst + hicon;
    lst = blkdata(lstblk,ofs * nleg,ub4);
    if (triptoports(net,lst,nleg,tports)) break;
    for (n = 0; n <= nleg; n++) {
      port = tports[n];
      if (port >= portcnt) warning(0,"port #%u %x",n,port);
      else {
        pp = ports + port;
        info(0,"port #%u %u %s",n,port,pp->name);
      }
    }
  }
  return 0;
}

static int showconn(struct network *net,int all)
{
  struct port *pp,*ports = net->ports;
  ub4 portcnt = net->portcnt;
  ub4 nodep,noarr,nodeparr,oneroute,oneroutes,geocnt;
  ub4 port,ndep,narr,n;
  ub4 *drids,*arids;

  ub4 constats[256];
  ub4 depstats[256];
  ub4 arrstats[256];
  ub4 statmax = Elemcnt(depstats) - 1;
  ub4 hinda = 0;

  aclear(constats);
  aclear(depstats);
  aclear(arrstats);
  nodep = noarr = nodeparr = oneroutes = geocnt = 0;

  for (port = 0; port < portcnt; port++) {
    pp = ports + port;
    ndep = pp->ndep; narr = pp->narr;
    hinda = max(hinda,ndep+narr);
    drids = pp->drids; arids = pp->arids;
    oneroute = 1;
    if (ndep == 0 && narr == 0) {
      if (pp->geo) geocnt++;
      else {
        info(Iter,"port %u is unconnected %s",port,pp->iname);
        nodeparr++;
      }
      oneroute = 0;
    } else if (ndep == 0) {
      info(Iter,"port %u has no deps - %s",port,pp->iname);
      nodep++;
      if (narr > 1 && arids[0] != arids[1]) oneroute = 0;
    } else if (narr == 0) {
      info(Iter,"port %u has no arrs - %s",port,pp->iname);
      noarr++;
      if (ndep > 1 && drids[0] != drids[1]) oneroute = 0;
    } else {
      if (ndep > 1 && drids[0] != drids[1]) oneroute = 0;
      if (narr > 1 && arids[0] != arids[1]) oneroute = 0;
    }
    if (ndep < 16 && narr < 16) constats[(ndep << 4) | narr]++;
    if (narr) depstats[min(ndep,statmax)]++;
    if (ndep) arrstats[min(narr,statmax)]++;
    oneroutes += oneroute;
  }
  warn(CC0,"%u of %u ports without connection",nodeparr,portcnt);
  info(CC0,"%u of %u ports without departures",nodep,portcnt);
  info(CC0,"%u of %u ports without arrivals",noarr,portcnt);
  for (ndep = 0; ndep < 3; ndep++) {
    for (narr = 0; narr < 3; narr++) {
      n = constats[(ndep << 4) | narr];
      if (ndep == 0 && narr == 0) {
        if (n > geocnt) info(0,"%u unconnected port\as",n - geocnt);
      } else if (n) info(0,"%u port\as with %u dep\as and %u arr\as", n,ndep,narr);
    }
  }
  info0(0,"");
  for (ndep = 0; ndep < 8; ndep++) {
    n = depstats[ndep];
    if (n) info(0,"%u port\as with %u dep\as and 1+ arrs", n,ndep);
  }
  n = depstats[statmax];
  if (n) info(0,"%u port\as with %u+ deps and 1+ arrs", n,statmax);
  for (narr = 0; narr < 8; narr++) {
    n = arrstats[narr];
    if (n) info(0,"%u port\as with %u arr\as and 1+ deps", n,narr);
  }
  n = arrstats[statmax];
  if (n) info(0,"%u port\as with %u+ arrs and 1+ deps", n,statmax);
  infocc(all,0,"%u of %u ports on a single route",oneroutes,portcnt);
  net->hinda = hinda;
  return 0;
}

// initialize basic network, and connectivity for each number of stops
// the number of stops need to be determined such that all port pairs are reachable
int mknet(ub4 maxstop,struct network *net)
{
  ub4 portcnt = 0,hopcnt;
  ub4 nstop,histop,allhistop = hi32;
  int rv,netok = 0;
  void *vosm = NULL;

  if (dorun(FLN,Runmknet,0) == 0) return 0;

  portcnt = net->portcnt;
  hopcnt = net->hopcnt;

  if (portcnt == 0) return error0(0,"no mknet on 0 ports");
  if (hopcnt == 0) return error0(0,"no mknet on 0 hops");

  if (maxstop + 1 > Netn) return error(0,"max legs %u above compile-time %u",maxstop + 1,Netn);

  net->maxstop = maxstop;

  // fill default min transfer times. todo in config
  ub4 *mintts = globs.mintts;
  mkmintt(mintts,Airintbit,Airintbit,60);
  mkmintt(mintts,Airintbit,Airdombit,90);
  mkmintt(mintts,Airdombit,Airdombit,45);
  mkmintt(mintts,Airdombit,Airintbit,90);
  mkmintt(mintts,Airintbit,Railbit|Busbit|Taxibit|Ferrybit,45);
  mkmintt(mintts,Railbit|Busbit|Taxibit|Ferrybit,Airintbit,120);
  mkmintt(mintts,Airdombit,Railbit|Busbit|Taxibit|Ferrybit,30);
  mkmintt(mintts,Railbit|Busbit|Taxibit|Ferrybit,Airdombit,60);

  mkmintt(mintts,Busbit,Railbit|Busbit|Taxibit|Ferrybit,5);
  mkmintt(mintts,Railbit|Busbit|Taxibit|Ferrybit,Busbit,5);
  mkmintt(mintts,Railbit,Railbit,3);
  mkmintt(mintts,Railbit|Busbit|Taxibit|Ferrybit,Ferrybit,10);
  mkmintt(mintts,Ferrybit,Railbit|Busbit|Taxibit|Ferrybit,10);

  if (marklocal(net)) return 1;

  showconn(net,1);

  if (dorun(FLN,Runnetn,0)) {
    if (globs.nolotx == 0 && mklotx(net)) return warn0(Ret1,"lotx failed");
  }

  struct osminfo oi;
  if (*globs.osmfile) {
    vosm = readosm(globs.osmfile,&oi);
    if (vosm == NULL) return warn0(Ret1,"readosm failed");
    net->vosm = vosm;
    net->nidcnt = oi.nidcnt;
  }

  if (mkportreach(net)) return warn0(Ret1,"portreach failed");

  rv = mktaxi(net);
  if (rv) return warn0(Ret1,"mktaxi failed");

  rv = mkwalk(net);
  if (rv) return warn0(Ret1,"mkwalk failed");

  error_z(net->whopcnt,0);

  rv = mkfares(net);
  if (rv) return warn0(Ret1,"mkfares failed");

  showmodes(net);

  if (vosm && freeosm(vosm)) return warn0(Ret1,"freeosm failed");
  net->vosm = NULL;

  rv = markwhops(net);
  if (rv) return warn0(Ret1,"markwhops failed");

  showconn(net,0);

  if (dorun(FLN,Runnet0,0)) {

    if (globs.nogrid == 0) rv = mkgeogrid(net);
    else
    if (rv) return warn0(Ret1,"geogrid failed");

    rv = mknet0(net);
    if (rv) return warn(Ret1,"net0 returned %d",rv);
    netok = 1;

    rv = conchk(net);
    if (rv) return warn0(Ret1,"conchk failed");

    rv = mkxfers(net);
    if (rv) return warn0(Ret1,"mkxfers failed");
  }

  histop = maxstop;
  limit_gt(histop,Nstop,0);

  if (histop && dorun(FLN,Runnetn,0)) {

    if (prepnetev(net)) return warn0(Ret1,"subevs failed");

    for (nstop = 1; nstop <= histop; nstop++) {
      if (mk_netn(net,nstop,histop)) return warn0(Ret1,"netn failed");
      info(0,"nstop %u lstlen \ah%lu",nstop,net->lstlen[nstop]);
      if (net->lstlen[nstop] == 0) break;
      net->histop = nstop;
    }
    info0(0,"static network init done");
    allhistop = min(allhistop,net->histop);

  } else {
    info0(0,"no n-stop static network init");
    allhistop = 0;
  }

  if (netok == 0) return 0;

  net->histop = allhistop;

  net = getnet();
  for (nstop = 0; nstop <= maxstop && portcnt > 20000; nstop++) {
    acciadr(net->concnt + nstop);
    acciadr(net->conofs + nstop);
  }

  globs.netok = 1;
  return 0;
}

// check whether a triplet passes thru the given ports
int checktrip_fln(struct network *net,ub4 *legs, ub4 nleg,ub4 dep,ub4 arr,ub4 dist,ub4 fln)
{
  ub4 legno,legno2,leg,leg2,arr0,arr1,arr2,dep1,dep2,cdist;
  ub4 whopcnt = net->whopcnt;
  ub4 *portsbyhop = net->portsbyhop;
  ub4 *hopdist = net->hopdist;

  if (dep == arr) return errorfln(FLN,0,fln,"dep %u equals arr",arr);

  for (legno = 0; legno < nleg; legno++) {
    leg = legs[legno];
    if (leg >= whopcnt) return errorfln(FLN,0,fln,"leg %u invalid hop %u",legno,leg);
  }
  if (nleg > 2) {
    for (legno = 0; legno < nleg; legno++) {
      leg = legs[legno];
      dep1 = portsbyhop[leg * 2];
      arr1 = portsbyhop[leg * 2 + 1];
      for (legno2 = legno+1; legno2 < nleg; legno2++) {
        leg2 = legs[legno2];
        dep2 = portsbyhop[leg2 * 2];
        arr2 = portsbyhop[leg2 * 2 + 1];
        if (leg == leg2) return errorfln(FLN,0,fln,"leg %u hop %u equals next",legno,leg);
        if (dep1 == dep2) return errorfln(FLN,0,fln,"leg %u dep %u equals next",legno,dep1);

// dep 21319 arr 8676
// net 1822 dyn1 2-3-0-0 4241 dep1 21319 leg 0 == arr2 21319 leg 2
        if (dep1 == arr2) return errorfln(FLN,0,fln,"%u-%u dep1 %u leg %u == arr2 %u leg %u",dep,arr,dep1,legno,arr2,legno2); // todo

        if (legno2 != legno + 1) {
          if (arr1 == dep2) return errorfln(FLN,0,fln,"leg %u arr %u equals preceding dep",legno,arr1);
        }
        if (arr1 == arr2) return errorfln(FLN,0,fln,"leg %u arr %u equals leg %u/%u arr",legno,arr1,legno2,nleg);
      }
    }
  }

  leg = legs[0];
  dep1 = portsbyhop[leg * 2];
  arr0 = portsbyhop[leg * 2 + 1];
  if (dep1 != dep) return errorfln(FLN,0,fln,"leg 0 hop %u dep %u mismatches %u",leg,dep1,dep);

  cdist = hopdist[leg];

  leg = legs[nleg-1];
  arr1 = portsbyhop[leg * 2 + 1];

  if (arr1 != arr) return errorfln(FLN,0,fln,"leg %u arr %u mismatches %u",nleg-1,arr1,arr);

  for (legno = 1; legno < nleg; legno++) {
    leg = legs[legno];
    dep1 = portsbyhop[leg * 2];
    if (arr0 != dep1) return errorfln(FLN,0,fln,"leg %u arr %u mismatches dep %u",legno,arr0,dep1);
    arr0 = portsbyhop[leg * 2 + 1];
    cdist += hopdist[leg];
  }
  if (dist != hi32) {
    if (dist != cdist) return errorfln(FLN,0,fln,"dist %u mismatches %u",cdist,dist);
  }
  return 0;
}

// check whether a triplet passes thru the given ports
int checktrip3_fln(struct network *net,ub4 *legs, ub4 nleg,ub4 dep,ub4 arr,ub4 via,ub4 dist,ub4 fln)
{
  ub4 legno,leg,hdep;
  ub4 *portsbyhop = net->portsbyhop;
  int hasvia = 0;

  if (nleg < 2) return errorfln(FLN,0,fln,"%u leg\as",nleg);
  if (checktrip_fln(net,legs,nleg,dep,arr,dist,fln)) return 1;
  if (via == dep) return errorfln(fln,0,FLN,"via %u == dep",via);
  if (via == arr) return errorfln(fln,0,FLN,"via %u == arr",via);

  for (legno = 1; legno < nleg; legno++) {
    leg = legs[legno];
    hdep = portsbyhop[leg * 2];
    if (hdep == via) hasvia = 1;
  }
  if (hasvia == 0) return errorfln(fln,0,FLN,"via %u not visited for %u-%u",via,dep,arr);
  return 0;
}

int triptoports_fln(ub4 fln,struct network *net,ub4 *trip,ub4 triplen,ub4 *ports)
{
  ub4 leg,l,dep,arr = hi32;
  ub4 whopcnt = net->whopcnt;
  ub4 portcnt = net->portcnt;

  error_ge(triplen,Nleg);

  for (leg = 0; leg < triplen; leg++) {
    l = trip[leg];
    if (l >= whopcnt) return errorfln(fln,0,FLN,"leg %u hop %u above %u",leg,l,whopcnt);
    dep = net->portsbyhop[2 * l];
    error_ge(dep,portcnt);
    if (leg) {
      if (dep != arr) return errorfln(fln,0,FLN,"leg %u hop %u dep %u not connects to preceding arr %u",leg,l,dep,arr);
    }
    error_ge(dep,net->portcnt);
    arr = net->portsbyhop[2 * l + 1];
    error_ge(arr,portcnt);
    ports[leg] = dep;
  }
  ports[triplen] = arr;
  return 0;
}

const char *modename(enum txkind mode)
{
  switch(mode) {
  case Airdom: return "plane-dom";
  case Airint: return "plane-int";
  case Rail: return "train";
  case Bus: return "bus";
  case Ferry: return "ferry";
  case Taxi: return "taxi";
  case Walk: return "walk";
  case Unknown: case Kindcnt:  return "unknown";
  }
  return "n/a";
}

char hoptype(struct network *net,ub4 hop)
{
  if (hop < net->hopcnt) return 'b';
  else if (hop < net->chopcnt) return 'c';
  else if (hop < net->thopcnt) return 't';
  else return 'w';
}

ub4 fgeodist(struct port *pdep,struct port *parr,int silent)
{
  double dlat = pdep->rlat,dlon = pdep->rlon,alat = parr->rlat,alon = parr->rlon;

  if (pdep->lat == 0 || pdep->lon == 0 || parr->lat == 0 || parr->lon == 0) return 50000;

  double fdist = geodist(dlat,dlon,alat,alon,pdep->name);
  if (fdist > 1 || silent) return (ub4)(fdist + 0.5);

  ub4 dep = pdep->id;
  ub4 arr = parr->id;
  char *dname = pdep->name;
  char *aname = parr->name;
  double x = 180 / M_PI;
  info(Iter|V0,"port %u-%u distance %e for %f,%f - %f,%f %s to %s",dep,arr,fdist,dlat * x,dlon * x,alat * x,alon * x,dname,aname);
  return 1;
}

// find nearest port from coords. 2D bsearch version
ub4 geocode2(ub4 ilat,ub4 ilon,ub4 scale,ub1 txmask,struct myfile *rep)
{
  gnet *net = getnet();
  struct port *pp,*ports = net->ports;
  struct sport *sp,*sports = net->sports;
  ub4 portcnt = net->portcnt;
  ub4 sportcnt = net->sportcnt;
  ub4 xportcnt = portcnt + sportcnt;
  ub4 *latsort = net->latxsort;
  ub4 *latsortidx = net->latxsortidx;
  ub4 *lonsort = net->lonxsort;
  ub4 *lonsortidx = net->lonxsortidx;

  double lat = (double)ilat / (double)scale - 90;
  if (lat >= 90 || lat <= -90) { error(0,"lat %f out of range from %u scale %u",lat,ilat,scale); return hi32; }
  double lon = (double)ilon / (double)scale - 180;
  if (lon >= 180 || lon <= -180) { error(0,"lon %f out of range from %u scale %u",lon,ilon,scale); return hi32; }
  double rlat = lat * M_PI / 180;
  double rlon = lon * M_PI / 180;
  double x = 180 / M_PI;
  double dist,vdist,hdist,lodist = 1e+10;
  ub4 loid = hi32;

  double flat = (double)ilat * net->latscale / (double)scale;
  double flon = (double)ilon * net->lonscale / (double)scale;
  ub4 mlat = (ub4)(flat + 0.5);
  ub4 mlon = (ub4)(flon + 0.5);

  ub4 dir = 1;
  ub4 a,o,ar,or,ai,oi,al,ol;
  char desc[256];

  info(0,"geocode 2 %f,%f mask %x",lat,lon,txmask);

  a = bsearch4(latsort,xportcnt,mlat,FLN,"lat");
  o = bsearch4(lonsort,xportcnt,mlon,FLN,"lon");
  a = min(a,xportcnt-1);
  o = min(o,xportcnt-1);
  info(0,"initial pos %u,%u of %u",a,o,xportcnt);

  ar = al = a;
  or = ol = o;

  dist = vdist = hdist = 1e10;

  ub4 iter = 0,iterlim = max(xportcnt / 4,20);
  while (iter < iterlim) {

    iter++;

    if (a < xportcnt) {
      ai = latsortidx[a];
      if (ai < portcnt) {
        pp = ports + ai;
        info(0,"port %u nd %u na %u modes %x %s",ai,pp->ndep,pp->narr,pp->modes,pp->iname);
        if (pp->valid && (pp->modes & txmask) && pp->nda && pp->infconcnt > 20) {
          fmtstring(desc,"a port %u %s",ai,pp->name);
          dist = geodist(rlat,rlon,pp->rlat,pp->rlon,desc);
          if (dist < lodist) { lodist = dist; loid = ai; }
          else {
            vdist = geodist(rlat,rlon,pp->rlat,rlon,desc);
            if (vdist >= lodist) {
              if (dir) al = xportcnt; else ar = xportcnt;
            }
          }
        } else info(0,"skip port %u nd %u na %u modes %x %s",ai,pp->ndep,pp->narr,pp->modes,pp->iname);
      } else {
        sp = sports + ai - portcnt;
        if (sp->modes & txmask) { // todo infcon from parent
          fmtstring(desc,"b port %u %s",ai,sp->name);
          dist = geodist(rlat,rlon,sp->rlat,sp->rlon,desc);
          if (dist < lodist) { lodist = dist; loid = ai; }
          else {
            vdist = geodist(rlat,rlon,sp->rlat,rlon,desc);
            if (vdist >= lodist) {
              if (dir) al = xportcnt; else ar = xportcnt;
            }
          }
        }
      }
    }

    if (o < xportcnt) {
      oi = lonsortidx[o];
      if (oi < portcnt) {
        pp = ports + oi;
        info(0,"port %u nd %u na %u modes %x %s",oi,pp->ndep,pp->narr,pp->modes,pp->iname);
        if (pp->valid && (pp->modes & txmask) && pp->nda && pp->infconcnt > 20) {
          fmtstring(desc,"c port %u %s",oi,pp->name);
          dist = geodist(rlat,rlon,pp->rlat,pp->rlon,desc);
          if (dist < lodist) { lodist = dist; loid = oi; }
          else {
            hdist = geodist(rlat,rlon,rlat,pp->rlon,desc);
            if (hdist >= lodist) {
              if (dir) ol = xportcnt; else or = xportcnt;
            }
          }
        } else info(0,"skip port %u nd %u na %u modes %x %s",oi,pp->ndep,pp->narr,pp->modes,pp->iname);
      } else {
        sp = sports + oi - portcnt;
        if (sp->modes & txmask) {
          fmtstring(desc,"d port %u %s",oi,sp->name);
          dist = geodist(rlat,rlon,sp->rlat,sp->rlon,desc);
          if (dist < lodist) { lodist = dist; loid = oi; }
          else {
            hdist = geodist(rlat,rlon,rlat,sp->rlon,desc);
            if (hdist >= lodist) {
              if (dir) ol = xportcnt; else or = xportcnt;
            }
          }
        }
      }
    }
    // info(0,"iter %u dir %u lodist %e vdist %e hdist %e al %u ar %u ol %u or %u",iter,dir,lodist,vdist,hdist,al,ar,ol,or);

    if (dir) {
      if (ar + 1 < xportcnt) a = ++ar;
      else a = xportcnt;
      if (or + 1 < xportcnt) o = ++or;
      else o = xportcnt;
    } else {
      if (al && al < xportcnt) a = --al; else a = al = xportcnt;
      if (ol && ol < xportcnt) o = --ol; else o = ol = xportcnt;
    }
    if ( (ar == xportcnt && al == xportcnt) || (or == xportcnt && ol == xportcnt) ) break;
    dir ^= 1;
  }

  if (loid == hi32) {
    warn(0,"no geocode match in %u iters",iter);
    return hi32;
  }

  //  reqid \t dist \t lat \t lon \t id \t pid \t modes \t name \t pname",0);

  double clat,clon;
  ub4 idist = (ub4)lodist;
  ub4 mdist = (ub4)(lodist * 1000 / Geoscale);
  rep->buf = rep->localbuf;

  if (loid < portcnt) {
    pp = ports + loid;
    clat = pp->rlat * x;
    clon = pp->rlon * x;
    info(0,"\ag%u from port %u at %f,%f %s %s iters %u",idist,loid,clat,clon,pp->name,pp->intname,iter);
    rep->len = fmtstring(rep->localbuf,".geo\t0\t%u\t%f\t%f\t%u\t%u\t%u\t%s\t%s\n",mdist,clat,clon,loid,loid,pp->modes,pp->name,pp->name);
  } else {
    sp = sports + loid - portcnt;
    clat = sp->rlat * x;
    clon = sp->rlon * x;
    pp = ports + sp->parent;
    info(0,"\ag%u from sport %u port %u at %f,%f %s %s iters %u",idist,loid,sp->parent,clat,clon,sp->name,sp->intname,iter);
    rep->len = fmtstring(rep->localbuf,".geo\t0\t%u\t%f\t%f\t%u\t%u\t%u\t%s\t%s\n",mdist,clat,clon,loid,sp->parent,sp->modes,sp->name,pp->name);
  }

  info(0,"%s",rep->localbuf);
  return loid;
}

// find nearest port from coords. Linear version
int geocode(ub4 ilat,ub4 ilon,ub4 scale,ub1 txmask,struct myfile *rep)
{
  double lat = (double)ilat / (double)scale - 90;
  double lon = (double)ilon / (double)scale - 180;
  double rlat = lat * M_PI / 180;
  double rlon = lon * M_PI / 180;
  double x = 180 / M_PI;
  double lolat,lolon;
  double dist,lodist = 1e+10;
  ub4 mdist,losport = hi32,loport = hi32;

  info(0,"scale %u lat %f lon %f %f %f mask %x",scale,lat,lon,rlat,rlon,txmask);

  gnet *net = getnet();
  struct port *pp,*lopp,*ports = net->ports;
  struct sport *sp,*losp,*sports = net->sports;
  ub4 port,portcnt = net->portcnt;
  ub4 sport,sportcnt = net->sportcnt;

  lopp = NULL;
  losp = NULL;

  for (sport = 0; sport < sportcnt; sport++) {
    sp = sports + sport;
    if ((sp->modes & txmask) == 0) continue;
    dist = geodist(rlat,rlon,sp->rlat,sp->rlon,sp->name);
    if (dist < lodist) { lodist = dist; losport = sport; losp = sp; }
    else if (dist >= Georange) return 1;
  }
  for (port = 0; port < portcnt; port++) {
    pp = ports + port;
    if ((pp->modes & txmask) == 0) continue;
    if (pp->nda == 0) continue;
    if (pp->subcnt) continue;
    dist = geodist(rlat,rlon,pp->rlat,pp->rlon,pp->name);
    if (dist < lodist) { lodist = dist; loport = port; lopp = pp; }
    else if (dist >= Georange) return 1;
  }
  mdist = (int)(lodist * 1000 / Geoscale);

  //  reqid \t dist \t lat \t lon \t id \t pid \t modes \t name \t pname",0);

  if (loport != hi32) {
   lolat = lopp->rlat * x;
   lolon = lopp->rlon * x;
   rep->len = fmtstring(rep->localbuf,".geo\t0\t%u\t%f\t%f\t%u\t%u\t%u\t%s\t%s\n",mdist,lolat,lolon,loport,loport,lopp->modes,lopp->name,lopp->name);
   info(0,"\ag%u from port %u at %f,%f %s",(ub4)lodist,loport,lolat,lolon,lopp->name);
  } else if (losport != hi32) {
   lolat = losp->rlat * x;
   lolon = losp->rlon * x;
   rep->len = fmtstring(rep->localbuf,".geo\t0\t%u\t%f\t%f\t%u\t%u\t%u\t%s\t%s\n",mdist,lolat,lolon,losport + portcnt,losp->parent,losp->modes,losp->name,"(n/a)");
   info(0,"\ag%u from sport %u at %f,%f %s",(ub4)lodist,losport,lolat,lolon,losp->name);
  } else { warn(0,"no geocode port for %f , %f",lat,lon); return 1; }
  rep->buf = rep->localbuf;
  return info(0,"%s",rep->localbuf);
}

static void filltt(ub4 *tts,ub4 dep,ub4 arrmask,ub4 val)
{
  ub4 x = dep << 4;

  if (arrmask & Airintbit) tts[x | Airint] = val;
  if (arrmask & Airdombit) tts[x | Airdom] = val;
  if (arrmask & Railbit) tts[x | Rail] = val;
  if (arrmask & Busbit) tts[x | Bus] = val;
  if (arrmask & Ferrybit) tts[x | Ferry] = val;
  if (arrmask & Taxibit) tts[x | Taxi] = val;
  if (arrmask & Walkbit) tts[x | Walk] = val;
}

void mkmintt(ub4 *tts,ub4 depmask,ub4 arrmask,ub4 val)
{
  if (depmask & Airintbit) filltt(tts,Airint,arrmask,val);
  if (depmask & Airdombit) filltt(tts,Airdom,arrmask,val);
  if (depmask & Railbit) filltt(tts,Rail,arrmask,val);
  if (depmask & Busbit) filltt(tts,Bus,arrmask,val);
  if (depmask & Ferrybit) filltt(tts,Ferry,arrmask,val);
  if (depmask & Taxibit) filltt(tts,Taxi,arrmask,val);
  if (depmask & Walkbit) filltt(tts,Walk,arrmask,val);
}

__attribute__ ((format (printf,5,6)))
int hopmsgfln(ub4 fln,ub4 lvl,ub4 code,ub4 hop,const char *fmt,...)
{
  int rv;
  char buf[4096];
  char buf2[4096];
  char c12[64];
  lnet *net = getnet();
  struct chop *hp,*hops = net->chops;
  struct port *pdep,*parr,*ports = net->ports;
  va_list ap;
  ub4 hopcnt = max(net->chopcnt,net->whopcnt);

  if (globs.msglvl < lvl) return (code & Ret1 ? 1 : 0);

  if (lvl < Error) code |= Exit;
  if (hops == NULL) return errorfln(FLN,code,fln,"nil chops for %s",fmt);
  if (hop >= hopcnt) return errorfln(FLN,code,fln,"hop %u above %u for %s",hop,hopcnt,fmt);
  hp = hops + hop;
  pdep = ports + hp->dep;
  parr = ports + hp->arr;

  va_start(ap, fmt);
  myvsnprintf(buf,0,sizeof(buf),fmt,ap);
  va_end(ap);

  if (hop >= net->hopcnt && hop < net->chopcnt) fmtstring(c12," =%u,%u",hp->hop1,hp->hop2);
  else *c12 = 0;
  fmtstring(buf2,"%c%chop %u%s %s",hp->ctype,hp->ckind ? hp->ckind : '?',hop,c12,buf);

  switch (lvl) {
  case Fatal: fatalfln(fln,code,FLN,"%s",buf2);
  case Error: rv = errorfln(fln,code,FLN,"%s",buf2); break;
  case Warn: rv = warnfln(fln,code,"%s",buf2); break;
  case Info: rv = infofln(fln,code,"%s",buf2); break;
  case Vrb: rv = vrbfln(fln,code,"%s",buf2); break;
  default: fatalfln(fln,code,FLN,"%s",buf2);
  }
  infofln(fln,Nolvl,"  net.%u '%.80s' to '%.80s'",__LINE__,pdep->name,parr->name);
  return rv;
}

#if 0
ub4 getmintt(ub4 *tts,ub4 depkind,ub4 arrkind)
{
  ub4 tt = tts[(depkind << 4) | arrkind];
  return tt;
}
#endif
