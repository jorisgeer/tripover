// osm.c - handle openstreetmap data

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2015-2016 Joris van der Geer.
 */

/*
  - Read input data
  - Reconstruct road network
  - Plan a road trip
 */

#include <string.h>
#include <stdlib.h>
#include <stdarg.h>

#include "base.h"
struct globs globs;

#include "os.h"
#include "mem.h"
#include "util.h"

static ub4 msgfile;
#include "msg.h"

#include "math.h"
#include "time.h"

#include "osm.h"
#include "osmint.h"
#include "osmnet.h"

static ub4 msgrep[8192];
#define Msgrep (msgrep[min(__LINE__,8191)]++ < 100)

static const double pi180 = M_PI / 180;

int iniosm(void)
{
  iniassert();
  msgfile = setmsgfile(__FILE__);
  return 0;
}

static int mkgeosort(struct onet *on,enum osmodes mode)
{
  ub4 cnt = on->nidcnt;
  ub4 ncnt = 0;
  struct node *np,*nodes = on->nodes;
  struct way *wp,*ways = on->ways;
  ub4 dep,idx,wid;
  ub1 modes;
  error_ge(mode,Osmodecnt);

  if (cnt < 2) return error(0,"no nodes for %u",cnt);
  info(0,"sorting \ah%u nodes",cnt);

  ub8 xlat,*latxsort = talloc(cnt,ub8,0,"geo lat",cnt);
  ub8 xlon,*lonxsort = talloc(cnt,ub8,0,"geo lon",cnt);
  ub4 lat,lon;

  sb8 slat,slon;

  // prepare bsearch for geo lookup
  for (dep = 0; dep < cnt; dep++) {
    np = nodes + dep;
    if (np->jid == hi32) continue;
    wid = np->wid;
    if (wid == hi32) continue;
    wp = ways + wid;
    modes = wp->modes;
    if (wp->jcnt == 0 || (mode & modes) == 0) continue;

    slat = (sb8)np->ilat + 90 * Osmgeoscale;
    slon = (sb8)np->ilon + 180 * Osmgeoscale;
    lat = (ub4)slat;
    lon = (ub4)slon;
    xlat = (ub8)lat << 32 | dep;
    xlon = (ub8)lon << 32 | dep;
    latxsort[ncnt] = xlat;
    lonxsort[ncnt] = xlon;
    ncnt++;
  }
  info(0,"\ah%u from \ah%u mode %u nodes",ncnt,cnt,mode);
  error_lt(ncnt,2);
  ub4 *latsort = alloc(ncnt,ub4,0,"geo lat",0);
  ub4 *lonsort = alloc(ncnt,ub4,0,"geo lon",0);
  ub4 *latsortidx = alloc(ncnt,ub4,0,"geo latidx",0);
  ub4 *lonsortidx = alloc(ncnt,ub4,0,"geo lonidx",0);

  sort8(latxsort,ncnt,FLN,"latsort");
  sort8(lonxsort,ncnt,FLN,"lonsort");

  // separate sorted list into coord and index
  for (idx = 0; idx < ncnt; idx++) {
    xlat = latxsort[idx];
    xlon = lonxsort[idx];
    lat = (ub4)(xlat >> 32);
    lon = (ub4)(xlon >> 32);
    dep = (ub4)xlat & hi32;
    latsort[idx] = lat;
    latsortidx[idx] = dep;
    dep = (ub4)xlon & hi32;
    lonsort[idx] = lon;
    lonsortidx[idx] = dep;
  }
  afree(latxsort,"geo lat");
  afree(lonxsort,"geo lon");

  on->latsorts[mode] = latsort;
  on->lonsorts[mode] = lonsort;
  on->latsortidxs[mode] = latsortidx;
  on->lonsortidxs[mode] = lonsortidx;
  on->sortcnts[mode] = ncnt;

  return info(0,"done sorting \ah%u %u nodes",cnt,mode);
}

ub4 lookupnid(void *von,ub4 ilat,ub4 ilon,enum osmodes mode,ub4 *pdist)
{
  error_ge(mode,Osmodecnt);
  struct onet *on = (struct onet *)von;
  struct node *pp,*nodes = on->nodes;
  ub4 nidcnt = on->nidcnt;
  ub4 sortcnt = on->sortcnts[mode];
  error_lt(sortcnt,2);

  ub4 *latsort = on->latsorts[mode];
  ub4 *lonsort = on->lonsorts[mode];
  ub4 *latsortidx = on->latsortidxs[mode];
  ub4 *lonsortidx = on->lonsortidxs[mode];
  double rlat,rlon;
  double dist,vdist,hdist,lodist;

  ub4 dir = 1;
  ub4 a,o,ar,or,ai,oi,al,ol,loid;
  int dbg = 0;
  // int dbg = (ilat == 590319690 && ilon == 3157494140);

  ub4 iter,iterlim = max(nidcnt / 500,5000);
  iterlim = min(iterlim,nidcnt);

  error_zp(latsort,nidcnt);

  rlat = lat2rad(ilat,Osmgeoscale);
  rlon = lon2rad(ilon,Osmgeoscale);

  a = bsearch4(latsort,sortcnt,ilat,FLN,"lat");
  o = bsearch4(lonsort,sortcnt,ilon,FLN,"lon");
  a = min(a,sortcnt-1);
  o = min(o,sortcnt-1);
  infocc(dbg,0,"initial pos %u,%u of %u",a,o,sortcnt);

  ar = al = a;
  or = ol = o;

  dist = vdist = hdist = lodist = 1e10;
  loid = hi32;
  pp = nodes;

  iter = 0;
  while (iter++ < iterlim) {

    if (a < sortcnt) {
      ai = latsortidx[a];
      pp = nodes + ai;
      dist = geodist(rlat,rlon,pp->rlat,pp->rlon,sp->name);
      infocc(dbg,0,"dist \ag%u \ar%f,\ar%f",(ub4)dist,pp->rlat,pp->rlon);
      if (dist < lodist) { lodist = dist; loid = ai; }
      else if (dist > Georange - 1) warn(0,"geo poi %u",ai);
      else {
        vdist = geodist(rlat,rlon,pp->rlat,rlon,sp->name);
        if (vdist > lodist) {
          if (dir) al = sortcnt; else ar = sortcnt;
        } else if (vdist > Georange - 1) warn(0,"geo poi %u",ai);
      }
    }

    if (o < sortcnt) {
      oi = lonsortidx[o];
      pp = nodes + oi;
      dist = geodist(rlat,rlon,pp->rlat,pp->rlon,"");
      infocc(dbg,0,"dist \ag%u",(ub4)dist);
      if (dist < lodist) { lodist = dist; loid = oi; }
      else if (dist > Georange - 1) warn(0,"geo poi %u",oi);
      else {
        hdist = geodist(rlat,rlon,rlat,pp->rlon,sp->name);
        if (hdist > lodist) {
          if (dir) ol = sortcnt; else or = sortcnt;
        } else if (hdist > Georange - 1) warn(0,"geo poi %u",oi);
      }
    }

    infocc(dbg,0,"iter %u dir %u lodist %f vdist %f hdist %f al %u ar %u ol %u or %u",iter,dir,lodist,vdist,hdist,al,ar,ol,or);

    if (dir) {
      if (ar + 1 < sortcnt) a = ++ar;
      else a = sortcnt;
      if (or + 1 < sortcnt) o = ++or;
      else o = sortcnt;
    } else {
      if (al && al < sortcnt) a = --al; else a = al = sortcnt;
      if (ol && ol < sortcnt) o = --ol; else o = ol = sortcnt;
    }
    if ( (ar == sortcnt && al == sortcnt) || (or == sortcnt && ol == sortcnt) ) break;
    dir ^= 1;
  } // each iter

  if (loid == hi32) {
    warn(Iter,"no geocode match in %u iters",iter);
    *pdist = hi32;
    return loid;
  }
  if (loid >= nidcnt) {
    error(0,"nid %u out of range %u for \ar%f,\ar%f",loid,sortcnt,rlat,rlon);
    return hi32;
  }
  pp = nodes + loid;

  ub4 fdist = (ub4)(lodist + 0.5);
  infocc(fdist > 20,V0,"\ar%f,\ar%f -> \ar%f,\ar%f in %u iter\as at \ag%u",rlat,rlon,pp->rlat,pp->rlon,iter,fdist);
  infocc(fdist > 50 * 100,0,"\ar%f,\ar%f -> \ar%f,\ar%f in %u iter\as at \ag%u mode %u nid %u %u-%u",rlat,rlon,pp->rlat,pp->rlon,iter,fdist,mode,loid,ilat,ilon);

  *pdist = fdist;
  return loid;
}

static void mapclean(ub4 *map,ub8 *dists,ub4 *times,ub4 *mapuse,ub4 usecnt,ub4 joincnt)
{
  ub4 n,jid;

  for (n = 0; n < usecnt; n++) {
    jid = mapuse[n];
    error_ge(n,joincnt);
    map[jid] = hi32;
    dists[jid] = hi64;
    times[jid] = hi32;
  }
#if 0
  for (jid = 0; jid < joincnt; jid++) {
    error_ne(map[jid],hi32);
    error_ne(dists[jid],hi32);
    error_ne(times[jid],hi32);
  }
#endif
}

static const ub4 iterlimit = 10000;

// actual trip planning. Elementary breadth-first version
int osmplan(void *vosm,ub4 depnid,ub4 arrnid,ub4 distlim10,enum osmodes mode,enum osmopt opts,struct osmres *res)
{
  struct onet *on = (struct onet *)vosm;
  struct node *nodes = on->nodes;
  struct node *np,*pdep = nodes + depnid;
  struct node *parr = nodes + arrnid;
  struct way *wp,*ways = on->ways;
  struct join *jp1,*joins = on->joins;
  ub4 waycnt = on->waycnt;
  ub4 *map = on->map;
  ub8 *dists = on->dists;
  ub4 *times = on->times;
  ub4 *mapuse = on->mapuse;
  ub4 *lst,*newlst,*tmplst;
  ub4 *jsp,*joinlst = on->joinlst;
  ub2 *jposp,*joinposlst = on->joinposlst;
  ub4 *wsp;
  ub4 n,usecnt = 0;
  ub4 joincnt = on->joincnt;
  ub2 pos1,pos2,*wposp;
  ub4 *nidgeop;

  ub4 wid,djid,ajid,jid1,jid2,nid,lonid;
  ub4 jcnt,cnt,newcnt,wcnt;
  ub4 l,w,j;
  ub8 dist = 0,dist0,dist2;
  ub4 dirdist,dist10;
  float minmtr,ftime;
  double fdist0,lodist;
  ub8 distlim = distlim10 * 10;
  ub4 rtime,ctime,time0 = 0;
  ub4 iter = 0, iter2 = 0;
  int show = opts & Osm_show;

  on->plancnt++;

  res->dist = hi32;
  res->time = hi32;

  if (depnid == arrnid) return error(0,"osmplan: dep %u equals arr",depnid);
  jid1 = pdep->jid;
  jid2 = parr->jid;

  if (jid1 == hi32) {
    wid = pdep->wid;
    error_ge(wid,waycnt);
    wp = ways + wid;
    error_z(wp->jcnt,wid);
    jid1 = joinlst[wp->jofs];
    warn(0,"move to jid %u for dep %u",jid1,depnid);
  }

  if (jid2 == hi32) {
    wid = parr->wid;
    if (wid == hi32) error(Exit,"arrnid %u no wid depnid %u",arrnid,depnid);
    error_ge(wid,waycnt);
    wp = ways + wid;
    error_z(wp->jcnt,wid);
    jid2 = joinlst[wp->jofs];
    warn(0,"move to jid %u for arr %u",jid2,arrnid);
  }

  djid = jid1;
  ajid = jid2;

  fdist0 = geodist(pdep->rlat,pdep->rlon,parr->rlat,parr->rlon,"osm");
  dirdist = (ub4)(fdist0 + 0.5);

  infocc(show,0,"plan %u-%u \ar%f,\ar%f \ar%f,\ar%f \ag%u",depnid,arrnid,pdep->rlat,pdep->rlon,parr->rlat,parr->rlon,dirdist);

  error_ge(jid1,joincnt);
  error_ge(jid2,joincnt);

  lst = on->lst1;
  newlst = on->lst2;

  // start with dep only
  lst[0] = djid;
  cnt = 1;
  map[djid] = djid;
  dists[djid] = 0;
  times[djid] = 0;
  mapuse[usecnt++] = djid;

  infocc(show,0,"plan %u-%u jids %u-%u",depnid,arrnid,jid1,jid2);

  while (cnt && map[ajid] == hi32 && iter++ < iterlimit) {

    msgprefix(0,"iter %u",iter);

    infocc(show && iter < 100,0,"cnt %u ",cnt);

    newcnt = 0;

    // for each join in worklist
    for (l = 0; l < cnt; l++) {
      jid1 = lst[l];
      error_ge(jid1,joincnt);
      error_eq(jid1,ajid);
      error_eq(map[jid1],hi32);
      dist0 = dist = dists[jid1];
      time0 = rtime = times[jid1];
      if (dist0 == hi64) {
        error(0,"no dist for jid %u",jid1);
        continue;
      }

//    info(0,"jid %u",jid1);
      jp1 = joins + jid1;
      wsp = jp1->ways;
      wposp = jp1->waypos;
      wcnt = jp1->wcnt;
      // infocc(jid1 == 733306 || jid1 == 733303,0,"jid %u cnt %u",jid1,wcnt);

      // for each way in join
      for (w = 0; w < wcnt; w++) {
        wid = wsp[w];
        pos1 = wposp[w];
        wp = ways + wid;
        if ( (wp->modes & mode) == 0) continue;
        error_ge(pos1,wp->ncnt);
        nidgeop = on->nidgeo + wp->nofs;
        jcnt = wp->jcnt;
        jsp = joinlst + wp->jofs;
        jposp = joinposlst + wp->jofs;
        error_z(jcnt,wid);
        minmtr = 60.0F / (1000.0F * wp->speed);

        // for each join in way
        for (j = 0; j < jcnt && newcnt < joincnt; j++) {
          jid2 = jsp[j];
          if (jid2 == jid1 || jid2 == djid) continue;
          pos2 = jposp[j];
          if (pos2 > pos1) {
            if (nidgeop[pos2] < nidgeop[pos1]) { error(0,"jid %u pos1 %u pos2 %u",jid2,pos1,pos2); continue; }
            dist2 = nidgeop[pos2] - nidgeop[pos1];
          // else if (pos2 == pos1) continue;
          } else {
            if (nidgeop[pos1] < nidgeop[pos2]) { error(0,"jid %u pos1 %u pos2 %u",jid2,pos1,pos2); continue; }
            dist2 = nidgeop[pos1] - nidgeop[pos2];
          }
          ftime = minmtr * (float)dist2 + 0.5F;
          rtime = (ub4)(ftime + 0.5F);
          ctime = rtime + time0;
          dist = dist0 + dist2;
          // info(0,"dist \ag%u + \ag%u",dist0,dist2);
          // infocc(jid1 == 733306 || jid1 == 733303,0,"jid %u dist %u %u",jid2,dist,dists[jid2]);
          if (dists[jid2] == hi64) { // first arrival
            if (dist < distlim) {
              dists[jid2] = dist;
              times[jid2] = ctime;
              map[jid2] = jid1;
              newlst[newcnt++] = jid2;
              mapuse[usecnt++] = jid2;
            }
          } else if (mode == Osfoot && dist < dists[jid2] && map[jid1] != jid2 && map[jid2] != jid1) {
            dists[jid2] = dist;
            times[jid2] = ctime;
            map[jid2] = jid1;
          } else if (mode == Oscar && ctime < times[jid2] && map[jid1] != jid2 && map[jid2] != jid1) {
            dists[jid2] = dist;
            times[jid2] = ctime;
            map[jid2] = jid1;
          }
          error_ge(usecnt,joincnt);
          if (jid2 == ajid) break;
        }
        if (j < jcnt) break;
      }
      if (w < wcnt) break;
    }
    infocc(show,0,"dist %u \ag%u",(ub4)(dist / 10),(ub4)(dist / 10));
    tmplst = newlst;
    newlst = lst;
    lst = tmplst;
    cnt = newcnt;
  }
  msgprefix(0,NULL);

  if (iter >= iterlimit) {
    mapclean(map,dists,times,mapuse,usecnt,joincnt);
    on->noplancnt++;
    return info(0,"reached iter limit %u",iter);
  } else if (cnt == 0) { // if stuck, check if reached nearby
    lodist = 1e10;
    lonid = depnid;
    for (n = 0; n < usecnt; n++) {
      jid1 = mapuse[n];
      nid = joins[jid1].nid;
      np = nodes + nid;
      fdist0 = geodist(np->rlat,np->rlon,parr->rlat,parr->rlon,"osm");
      if (fdist0 < 10) {
        ajid = jid1;
        break;
      }
      if (fdist0 < lodist) { lodist = fdist0; lonid = nid; }
    }
    if (n == usecnt) {
      mapclean(map,dists,times,mapuse,usecnt,joincnt);
      np = nodes + lonid;
      infocc(show,0,"cnt 0 at iter %u use %u \ar%f,\ar%f",iter,usecnt,np->rlat,np->rlon);
      on->noplancnt++;
      return 0;
    }
  }
  res->dist = (ub4)(dists[ajid] / 10);
  res->time = times[ajid];
  res->cnt = 1;
  infocc(show || iter > 100 || dist > 5000,0,"nid %u-%u in %u iters dist \ag%u time %u use %u",depnid,arrnid,iter,res->dist,times[ajid],usecnt);
  if (res->time == hi32) {
    warn(0,"no time for %u-%u",djid,ajid);
    if (mode == Oscar) res->dist = hi32;
  }
  if (res->dist > 10 && res->dist * 2 < dirdist) {
    warn(0,"node %u-%u road dist \ag%u below direct \ag%u",depnid,arrnid,res->dist,dirdist);
    res->dist = dirdist;
  }

  if (show == 0) {
    mapclean(map,dists,times,mapuse,usecnt,joincnt);
    return 0;
  }

  // show route
  jid1 = ajid;
  while (map[jid1] != jid1 && iter2++ < iter * 2) {
    error_eq(map[jid1],hi32);
    dist10 = (ub4)(dists[jid1] / 10);
    jid2 = map[jid1];
    jp1 = joins + jid1;
    np = nodes + jp1->nid;
    wid = jp1->ways[0];
    wp = ways + wid;
    info(Noiter," %u-%u '%s' \ar%f,\ar%f \ag%u",jid1,jid2,wp->name,np->rlat,np->rlon,dist10);
    jid1 = jid2;
  }
  mapclean(map,dists,times,mapuse,usecnt,joincnt);
  return 0;
}

static ub4 timelimit = 1000;

// Profile search: breadth-first, car only
int osmprofile(void *vosm,ub4 depnid,ub4 *nid2port,ub1 *portdup,ub4 portcnt,ub4 *ports,ub8 *portdts,ub4 distlim10,enum osmopt opts,struct osmres *res)
{
  struct onet *on = (struct onet *)vosm;
  ub4 nidcnt = on->nidcnt;
  error_ge(depnid,nidcnt);
  struct node *nodes = on->nodes;
  struct node *np,*pdep;
  struct way *wp,*ways = on->ways;
  struct join *jp1,*joins = on->joins;
  ub4 waycnt = on->waycnt;
  ub4 *map = on->map;
  ub8 *dists = on->dists;
  ub4 *times = on->times;
  ub4 *mapuse = on->mapuse;
  ub4 *lst,*newlst,*tmplst;
  ub4 *jsp,*joinlst = on->joinlst;
  ub2 *jposp,*joinposlst = on->joinposlst;
  ub4 *wsp;
  ub4 usecnt = 0;
  ub4 joincnt = on->joincnt;
  ub2 pos1,pos2,*wposp;
  ub4 *nidgeop;
  ub4 *jidref = on->jidref;
  ub4 wid,djid,jid1,jid2,nid;
  ub4 dep,arr,portndx = 0;
  ub8 portdt;
  ub4 jcnt,cnt,newcnt,wcnt;
  ub4 l,w,j;
  ub8 dist = 0,dist0,dist2;
  float minmtr,ftime;
  ub8 distlim = distlim10 * 10;
  ub4 rtime,ctime,time0 = 0;
  ub4 iter = 0;
  int show = opts & Osm_show;
  enum osmodes mode = Oscar;

  res->dist = hi32;
  res->time = hi32;

  // make jid portrefs from nid
  nsethi(jidref,joincnt);
  for (nid = 0; nid < nidcnt; nid++) {
    dep = nid2port[nid];
    if (dep == 0) continue;
    dep--;
    np = nodes + nid;
    jid1 = np->jid;

    if (jid1 == hi32) {
      wid = np->wid;
      error_ge(wid,waycnt);
      wp = ways + wid;
      error_z(wp->jcnt,wid);
      jid1 = joinlst[wp->jofs];
    }
    error_ge(jid1,joincnt);
    jidref[jid1] = dep;
  }

  pdep = nodes + depnid;
  jid1 = pdep->jid;

  if (jid1 == hi32) {
    wid = pdep->wid;
    error_ge(wid,waycnt);
    wp = ways + wid;
    error_z(wp->jcnt,wid);
    jid1 = joinlst[wp->jofs];
    warn(0,"move to jid %u for dep %u",jid1,depnid);
  }
  error_ge(jid1,joincnt);
  dep = jidref[jid1];

  djid = jid1;

  infocc(show,0,"profile nid %u jid %u \ar%f,\ar%f",depnid,djid,pdep->rlat,pdep->rlon);

  error_ge(jid1,joincnt);

  lst = on->lst1;
  newlst = on->lst2;

  // start with dep only
  lst[0] = djid;
  cnt = 1;
  map[djid] = djid;
  dists[djid] = 0;
  times[djid] = 0;
  mapuse[usecnt++] = djid;

  nclear(portdup,portcnt);

  setimer(timelimit,1);

  while (cnt && iter++ < iterlimit) {

    if (isalarm()) break;

    msgprefix(0,"iter %u",iter);

    infocc(show && iter < 100,0,"cnt %u ",cnt);

    newcnt = 0;

    // for each join in worklist
    for (l = 0; l < cnt; l++) {
      jid1 = lst[l];
      error_ge(jid1,joincnt);
      error_eq(map[jid1],hi32);
      dist0 = dist = dists[jid1];
      time0 = rtime = times[jid1];
      if (dist0 == hi64) {
        error(0,"no dist for jid %u",jid1);
        continue;
      }

//    info(0,"jid %u",jid1);
      jp1 = joins + jid1;
      wsp = jp1->ways;
      wposp = jp1->waypos;
      wcnt = jp1->wcnt;

      // for each way in join
      for (w = 0; w < wcnt; w++) {
        wid = wsp[w];
        pos1 = wposp[w];
        wp = ways + wid;
        if ( (wp->modes & mode) == 0) continue;
        error_ge(pos1,wp->ncnt);
        nidgeop = on->nidgeo + wp->nofs;
        jcnt = wp->jcnt;
        jsp = joinlst + wp->jofs;
        jposp = joinposlst + wp->jofs;
        error_z(jcnt,wid);
        minmtr = 60.0F / (1000.0F * wp->speed);

        // for each join in way
        for (j = 0; j < jcnt && newcnt < joincnt; j++) {
          jid2 = jsp[j];
          if (jid2 == jid1 || jid2 == djid) continue;
          pos2 = jposp[j];
          if (pos2 > pos1) {
            if (nidgeop[pos2] < nidgeop[pos1]) { error(0,"jid %u pos1 %u pos2 %u",jid2,pos1,pos2); continue; }
            dist2 = nidgeop[pos2] - nidgeop[pos1];
            dist = dist0 + dist2;
            if (dist > distlim) break;
          // else if (pos2 == pos1) continue;
          } else {
            if (nidgeop[pos1] < nidgeop[pos2]) { error(0,"jid %u pos1 %u pos2 %u",jid2,pos1,pos2); continue; }
            dist2 = nidgeop[pos1] - nidgeop[pos2];
            dist = dist0 + dist2;
            if (dist > distlim) continue;
          }
          ftime = minmtr * (float)dist2 + 0.5F;
          rtime = (ub4)(ftime + 0.5F);
          ctime = rtime + time0;
          dist = dist0 + dist2;
          // info(0,"dist \ag%u + \ag%u",dist0,dist2);
          // infocc(jid1 == 733306 || jid1 == 733303,0,"jid %u dist %u %u",jid2,dist,dists[jid2]);

          if (dists[jid2] == hi64) { // first arrival
            arr = jidref[jid2];
            if (arr != hi32) {
              error_ge(arr,portcnt);
//              pinfo = portinfos[dep];
//              sumreach = pinfo >> 32;
//              nda = (pinfo >> 16) & hi16;
              if (arr != dep && dist < distlim && portdup[arr] == 0) {
                portdup[arr] = 1;
                error_ge(portndx,portcnt);
                ports[portndx] = arr;
                portdt = (ub8)(dist / 10) << 32;
                portdt |= ctime;
                portdts[portndx++] = portdt;
              }
            }
            dists[jid2] = dist;
            times[jid2] = ctime;
            map[jid2] = jid1;
            newlst[newcnt++] = jid2;
            mapuse[usecnt++] = jid2;
          } else if (ctime < times[jid2] && map[jid1] != jid2 && map[jid2] != jid1) { // todo: also if dist << dists[]
            dists[jid2] = dist;
            times[jid2] = ctime;
            map[jid2] = jid1;
          }
          error_ge(usecnt,joincnt);
        }
        if (j < jcnt) break;
      }
      if (w < wcnt) break;
    }
    infocc(show,0,"dist \ag%u",(ub4)(dist / 10));
    tmplst = newlst;
    newlst = lst;
    lst = tmplst;
    cnt = newcnt;
  }
  msgprefix(0,NULL);
  setimer(0,1);

  res->cnt = portndx;

  mapclean(map,dists,times,mapuse,usecnt,joincnt);
  return info(0,"reached %u ports",portndx);
}

void osmstats(void *vosm)
{
  struct onet *on = (struct onet *)vosm;

  if (on == NULL) return;
  info(Noiter,"\ah%u plans, \ah%u noplan",on->plancnt,on->noplancnt);
}

static int rdosm(struct onet *on,const char *osmname)
{
  ub4 nid,wid,w;
  ub4 n,nofs,ncnt,wcnt;
  struct eta eta;

  info(0,"read %s",osmname);

  ub8 len;

  int fd = fileopen(osmname,1);
  if (fd == -1) return 1;

  struct myfile mf;
  if (osfdinfo(&mf,fd)) { fileclose(fd,osmname); return oserror(0,"cannot get file size for %s",osmname); }
  ub8 osmlen = mf.len;

  if (osmlen <= sizeof(struct osmhdr)) { fileclose(fd,osmname); return error(0,"%s is empty (%lu)",osmname,osmlen); }
  void *tosm = osmmapfd(osmlen,fd);
  if (tosm == NULL) {  fileclose(fd,osmname); return 1; }
  void *tpos = tosm;

  struct osmhdr hdr,*hp = (struct osmhdr *)tosm;
  ub4 *pmagic;

  tpos = hp + 1;

  hdr = *hp;
  ub4 nidcnt = hdr.nodecnt;
  ub4 waycnt = hdr.waycnt;
  ub4 nlstlen = hdr.nlstlen;

  if (hdr.magic != Omagic1) { osmunmap(tosm,osmlen); fileclose(fd,osmname); return error(0,"%s is not a valid osm.bin file",osmname); }
  if (nidcnt == 0) { osmunmap(tosm,osmlen); fileclose(fd,osmname); return error(0,"%s has no nodes",osmname); }
  if (waycnt == 0) { osmunmap(tosm,osmlen); fileclose(fd,osmname); return error(0,"%s has no ways",osmname); }
  if (nlstlen == 0) { osmunmap(tosm,osmlen); fileclose(fd,osmname); return error(0,"%s has no waynodes",osmname); }

  info(0,"\ah%u nodes \ah%u waynodes \ah%u ways",nidcnt,nlstlen,waycnt);

  pmagic = tpos;
  if (*pmagic != Omagic2) { osmunmap(tosm,osmlen); fileclose(fd,osmname); return error(0,"%s is not a valid osm.bin file",osmname); }
  tpos = pmagic + 1;

  // nodes
  ub8 nlen = nidcnt * sizeof(struct tnode);
  ub8 llen = nlstlen * 4;
  ub8 lglen = nlstlen * 4;
  ub8 wlen = waycnt * sizeof(struct tway);
  len = nlen + llen + lglen + wlen + sizeof(struct osmhdr);
  len += 3 * sizeof(ub4);

  if (len > osmlen) { osmunmap(tosm,osmlen); fileclose(fd,osmname); return error(0,"%s size expected %lu, actual %lu",osmname,len,osmlen); }
  else if (len != osmlen) warn(0,"%s size expected %lu, actual %lu",osmname,len,osmlen);

  info(0,"read \ah%u nodes",nidcnt);
  struct node *np,*nodes = alloc0(nidcnt,struct node,0);
  struct tnode *tnp = (struct tnode *)tpos;
  double flat,flon;

  for (nid = 0; nid < nidcnt; nid++) {
    np = nodes + nid;
    flat = (double)tnp->ilat / Osmgeoscale;
    flon = (double)tnp->ilon / Osmgeoscale;
    // info(0,"lat %f lon %f",flat,flon);
    np->ilat = tnp->ilat;
    np->ilon = tnp->ilon;
    np->rlat = flat * pi180;
    np->rlon = flon * pi180;
    np->jid = hi32;
    np->wid = hi32;
    tnp++;
  }
  tpos = tnp;

  pmagic = tpos;
  if (*pmagic != Omagic3) { osmunmap(tosm,osmlen); fileclose(fd,osmname); return error(0,"%s is not a valid osm.bin file",osmname); }
  tpos = pmagic + 1;

  // ways
  info(0,"read \ah%u waynodes",nlstlen);
  ub4 *nidlst = alloc0(nlstlen,ub4,0);
  ub4 *tnidlst = tpos;
  enum osmodes mode;
  memcpy(nidlst,tpos,llen);
  tpos = (tnidlst + nlstlen);

  info(0,"read \ah%u waynodes dist",nlstlen);
  ub4 *nidgeo = alloc0(nlstlen,ub4,0);
  ub4 *tgeolst = tpos;
  memcpy(nidgeo,tpos,lglen);
  tpos = (tgeolst + nlstlen);

  pmagic = tpos;
  if (*pmagic != Omagic4) { osmunmap(tosm,osmlen); fileclose(fd,osmname); return error(0,"%s is not a valid osm.bin file: expect magic %x, found %x",osmname,Omagic4,*pmagic); }
  tpos = pmagic + 1;

  info(0,"read \ah%u ways len",waycnt);
  struct way *wp,*ways = alloc0(waycnt,struct way,0);
  struct tway *twp = (struct tway *)tpos;
  for (wid = 0; wid < waycnt; wid++) {
    wp = ways + wid;
    ncnt = twp->ncnt;
    error_z(ncnt,wid);
    wp->ncnt = (ub2)ncnt;
    wp->nofs = twp->nofs;
    wp->speed = max(twp->speed,1);
    mode = 0;
    if (twp->modes & Twfoot) mode |= Osfoot;
    if (twp->modes & Twbike) mode |= Osbike;
    if (twp->modes & Twcar) mode |= Oscar;
    wp->modes = mode;
    memcpy(wp->name,twp->name,min(sizeof(twp->name),sizeof(wp->name)));
    twp++;
  }
  tpos = (char *)twp;

  osmunmap(tosm,osmlen);
  fileclose(fd,osmname);

  info(0,"done reading %s",osmname);

  // create derived data

  // joins
  ub2 *joincnts = alloc(nidcnt,ub2,0,"join cnts",0);
  ub4 *nid2jid = talloc0(nidcnt,ub4,0);
  ub4 *nodeway = alloc0(nlstlen,ub4,0);

  ub4 joincnt = 0;
  ub4 cnt,wnid,jid = 0;
  ub4 dist,prvdist;

  for (wid = 0; wid < waycnt; wid++) {
    wp = ways + wid;
    ncnt = wp->ncnt;
    nofs = wp->nofs;
    error_ge(nofs,nlstlen);
    error_gt((ub8)nofs+ncnt,(ub8)nlstlen,wid);
    prvdist = nidgeo[nofs];
    error_nz(prvdist,wid);
    for (n = 0; n < ncnt; n++) {
      nid = nidlst[nofs + n];
      dist = nidgeo[nofs + n];
      error_ge(nid,nidcnt);
      error_lt_cc(dist,prvdist,"wid %u pos %u ofs %u",wid,n,nofs);
      prvdist = dist;
      nodes[nid].wid = wid;
      nodeway[nofs + n] = wid;
    }
  }

  ub4 nowaycnt = 0;
  for (nid = 0; nid < nidcnt; nid++) {
    np = nodes + nid;
    if (np->wid == hi32) {
      infocc(Msgrep,0,"node %u no way",nid);
      nowaycnt++;
    }
  }
  info(CC0,"\ah%u of \ah%u nodes without way",nowaycnt,nidcnt);

  // count joins
  info(0,"count joins in \ah%u waynodes",nlstlen);
  for (wnid = 0; wnid < nlstlen; wnid++) {
    nid = nidlst[wnid];
    cnt = joincnts[nid];
    error_ovf(cnt,ub2);
    cnt++;
    joincnts[nid] = (ub2)cnt;
  }

  for (nid = 0; nid < nidcnt; nid++) {
    cnt = joincnts[nid];
    if (cnt < 2) continue;
    nid2jid[nid] = jid;
    jid++;
  }
  joincnt = jid;
  info(0,"\ah%u joins",joincnt);
  error_ne(joincnt,hdr.joincnt);

  struct join *jp,*joins = alloc(joincnt,struct join,0,"joins",0);

  info(0,"create joins for \ah%u waynodes",nlstlen);
  for (wnid = 0; wnid < nlstlen; wnid++) {
    nid = nidlst[wnid];
    cnt = joincnts[nid];
    if (cnt < 2) continue;
    jid = nid2jid[nid];
    wid = nodeway[wnid];
    wp = ways + wid;
    jp = joins + jid;
    jp->nid = nid;
    w = jp->wcnt;
    if (w + 1 >= Njoin) {
      warn(0,"jid %u wcnt %u",jid,w);
      continue;
    }
    jp->wcnt = w + 1;
    error_ge(w+1,Njoin);
    jp->ways[w] = wid;
    nofs = wp->nofs;
    error_lt(wnid,nofs);
    error_ge(wnid,nofs + wp->ncnt);
    jp->waypos[w] = (ub2)(wnid - nofs);
  }

  afree0(nid2jid);

  // create joins by way list
  ub4 jcnt;
  ub4 *wsp;
  ub2 pos,*wposp;
  ub4 jlstlen = 0;

  for (jid = 0; jid < joincnt; jid++) {
    if (progress(&eta,"join %u of %u  %u",jid,joincnt,jlstlen)) return 1;
    jp = joins + jid;
    nid = jp->nid;
    error_ge(nid,nidcnt);
    np = nodes + nid;
    np->jid = jid;
    wcnt = jp->wcnt;
    error_z(wcnt,jid);
    jlstlen += wcnt;
    wsp = jp->ways;
    for (w = 0; w < wcnt; w++) {
      wid = wsp[w];
      wp = ways + wid;
      if (wp->jcnt > 65530) return error(0,"jid %u way %u of %u cnt %u",jid,w,wcnt,wp->jcnt);
      wp->jcnt++;
    }
  }

  info(0,"\ah%u join list",jlstlen);
  ub4 *jlstp,*joinlst = alloc0(jlstlen,ub4,0);
  ub2 *jposlstp,*joinposlst = alloc0(jlstlen,ub2,0);
  ub4 jofs = 0;

  for (wid = 0; wid < waycnt; wid++) {
    wp = ways + wid;
    jcnt = wp->jcnt;
    // error_z(jcnt,wid);
    infocc(jcnt == 0,0,"wid %u no joins",wid);
    wp->jcnt = 0;  // refill next pass
    wp->jofs = jofs;
    jofs += jcnt;
  }

  for (jid = 0; jid < joincnt; jid++) {
    if (progress0(&eta,"join %u of %u",jid,joincnt)) return 1;
    jp = joins + jid;
    wcnt = jp->wcnt;
    wsp = jp->ways;
    wposp = jp->waypos;
    for (w = 0; w < wcnt; w++) {
      wid = wsp[w];
      pos = wposp[w];
      wp = ways + wid;
      jcnt = wp->jcnt;
      jlstp = joinlst + wp->jofs;
      jposlstp = joinposlst + wp->jofs;
      jlstp[jcnt] = jid;
      jposlstp[jcnt] = pos;
      error_ovf(jcnt,ub2);
      wp->jcnt = (ub2)(jcnt + 1);
    }
  }

  on->nidcnt = nidcnt;
  on->waycnt = waycnt;
  on->joincnt = joincnt;
  on->nlstlen = nlstlen;
  on->joinlst = joinlst;
  on->joinposlst = joinposlst;

  on->nodes = nodes;
  on->ways = ways;
  on->joins = joins;
  on->nidlst = nidlst;
  on->nidgeo = nidgeo;

  on->lst1 = alloc0(joincnt,ub4,0);
  on->lst2 = alloc0(joincnt,ub4,0);
  on->map = alloc0(joincnt,ub4,0xff);
  on->dists = alloc0(joincnt,ub8,0xff);
  on->times = alloc0(joincnt,ub4,0xff);
  on->mapuse = alloc0(joincnt,ub4,0);
  on->jidref = alloc0(joincnt,ub4,0);

  info0(0,"done processing osm");
  return 0;
}

static struct onet on;

void *readosm(const char *name,struct osminfo *oi)
{
  if (oi) oi->nidcnt = 0;
  if (rdosm(&on,name)) return NULL;
  if (oi) oi->nidcnt = on.nidcnt;
  if (mkgeosort(&on,Osfoot)) return NULL;
  if (mkgeosort(&on,Oscar)) return NULL;

  return &on;
}

static int freesort(enum osmodes mode)
{
  if (afree0(on.latsorts[mode])) return 1;
  if (afree0(on.lonsorts[mode])) return 1;
  if (afree0(on.latsortidxs[mode])) return 1;
  if (afree0(on.lonsortidxs[mode])) return 1;
  return 0;
}

int freeosm(void *vosm)
{
  if (vosm != &on) return error0(0,"unexpected osm ptr passed");

  if (afree0(on.joinlst)) return 1;
  if (afree0(on.joinposlst)) return 1;

  if (afree0(on.lst1)) return 1;
  if (afree0(on.lst2)) return 1;
  if (afree0(on.map)) return 1;
  if (afree0(on.dists)) return 1;
  if (afree0(on.times)) return 1;
  if (afree0(on.mapuse)) return 1;
  if (afree0(on.jidref)) return 1;

  if (freesort(Osfoot)) return 1;
  if (freesort(Oscar)) return 1;

  return 0;
}
