// netev.c - time events for prepared net

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2017 Joris van der Geer.
 */

#include <stddef.h>

#include "base.h"
#include "cfg.h"
#include "mem.h"

static ub4 msgfile;
#include "msg.h"

#include "iadr.h"
#include "math.h"
#include "time.h"
#include "util.h"
#include "net.h"
#include "netev.h"

// take at least span evs, aim at sub limit at max
#define Subsamples 16
#define Subperday 8
#define Subsamples2 32

void ininetev(void)
{

  msgfile = setmsgfile(__FILE__);
  iniassert();
}

static ub4 gst0,gst1;

int prepnetev(lnet *net)
{
  ub4 st0 = globs.pat0 * 1440;
  ub4 st1 = globs.pat1 * 1440;
  ub4 gt0 = net->t0;

  ub4 nt0 = net->tt0,nt1 = net->tt1;

  st0 = min(st0,nt1);
  st0 = max(st0,nt0);
  st1 = min(st1,nt1);
  st1 = max(st1,nt0);
  if (st1 <= st0)  return error(0,"no sampling time period at \ad%u - \ad%u",st0,st1);
  gst0 = st0 - gt0;
  gst1 = st1 - gt0;
  return 0;
}

#define Est_statlen (60 * 48)
static ub4 dtbins2[Nthread * Est_statlen];
static ub4 dtbins3[Nthread * Est_statlen];

enum Eststat { H12c,H123c,H1,H1dt,H2,H2dt,H3,H3dt,H12,H12dt,H123,H123dt,Hc1x,Hc11,Escnt };

static ub8 stat2_nocnt[Nthread * Escnt];
static ub8 stat3_nocnt[Nthread * Escnt];

void estdur2_stats(ub4 tid)
{
  ub8 sumcnt = 0,sumscnt = 0;
  ub8 *sp = stat2_nocnt + tid * Escnt;
  ub4 msgtid = (tid << Tidshift) | Tidbit;

  info(msgtid,"est2 nocnts: h12c \ah%lu h1 \ah%lu/\ah%lu h2 \ah%lu/\ah%lu h12 \ah%lu/\ah%lu hc1x \ah%lu hc11 \ah%lu",
    sp[H12c],sp[H1dt],sp[H1],sp[H2dt],sp[H2],sp[H12dt],sp[H12],sp[Hc1x],sp[Hc11]);

  nclear(sp,Escnt); // clear for next run

  ub4 i,scnt;
  ub4 dthibin = Est_statlen - 1;
  ub4 *bp = dtbins2 + tid * Est_statlen;
  for (i = 0; i <= dthibin; i++) sumscnt += bp[i];
  for (i = 0; i <= dthibin; i++) {
    scnt = bp[i];
    sumcnt += scnt;
    infocc(scnt,Notty|V0,"  dt %u cnt %u %lu%%",i,scnt,sumcnt * 100 / sumscnt);
  }
}

void estdur3_stats(ub4 tid)
{
  ub8 sumcnt = 0,sumscnt = 0;
  ub8 *sp = stat3_nocnt + tid * Escnt;
  ub4 msgtid = (tid << Tidshift) | Tidbit;

  info(msgtid,"est3 nocnts: h123c \ah%lu h1 \ah%lu/\ah%lu h2 \ah%lu/\ah%lu h3 \ah%lu/\ah%lu h123 \ah%lu/\ah%lu",
    sp[H123c],sp[H1dt],sp[H1],sp[H2dt],sp[H2],sp[H3dt],sp[H3],sp[H123dt],sp[H123]);

  nclear(sp,Escnt); // clear for next run

  ub4 i,scnt;
  ub4 dthibin = Est_statlen - 1;
  ub4 *bp = dtbins3 + tid * Est_statlen;
  for (i = 0; i <= dthibin; i++) sumscnt += bp[i];
  for (i = 0; i <= dthibin; i++) {
    scnt = bp[i];
    sumcnt += scnt;
    infocc(scnt,Notty|V0,"  dt %u cnt %u %lu%%",i,scnt,sumcnt * 100 / sumscnt);
  }
  estdur2_stats(tid);
}

ub4 lotx2(lnet *net,ub4 hop1,ub4 hop2,ub4 *phitx)
{
  ub4 chopcnt = net->chopcnt;
  struct chop *chp1,*chp2,*chops = net->chops;
  ub8 cx,cx2,*cev1,*cev2,*cevents = net->cevents;
  ub4 e1,e2;
  ub4 evcnt1,evcnt2;
  ub4 t1,t2,dur1,dur2,dift;
  ub4 gt0 = net->t0;
  int dbg = 0;

  *phitx = 0;
  error_ge(hop1,chopcnt);
  error_ge(hop2,chopcnt);

  chp1 = chops + hop1;
  chp2 = chops + hop2;
  error_eq(chp1->kind,Taxi);
  error_eq(chp2->kind,Taxi);

  cev1 = cevents + chp1->evofs;
  cev2 = cevents + chp2->evofs;

  evcnt1 = chp1->evcnt;
  evcnt2 = chp2->evcnt;
  error_z(evcnt1,hop1);
  error_z(evcnt2,hop2);

  if (evcnt1 == 0 || evcnt2 == 0) {
    return hi32;
  }

  ub4 lodur1 = chp1->lodur;
  ub4 hidur1 = chp1->hidur;

  t1 = chp1->t0 - gt0;
  e1 = 0;

  cx = cev1[0];
  ub4 chk = (cx >> Accshift) & 0xff;
  error_ne_cc(chk,hop1 & 0xff,"hop %u cx %lx ofs %lu evs %u",hop1,cx,chp1->evofs,evcnt1);
  dur1 = (cx >> Durshift) & Durlim;
  error_lt(dur1,lodur1);
  error_gt_cc(dur1,hidur1,"%chop %u",hoptype(net,hop1),hop1);

  ub4 tx,hitx = 0,lotx = hi32;

  for (e2 = 0; e2 < evcnt2; e2++) {
    cx2 = cev2[e2];

    t2 = (cx2 & Timlim);
    dur2 = (cx2 >> Durshift) & Durlim;

    if (t1 + dur1 > t2) continue;

    infocc(dbg,Notty,"e2 %2u dur %u at \ad%u",e2,dur2,t2+gt0);

    while (e1 + 1 < evcnt1) {
      cx = cev1[e1+1];
      dift = cx & Timlim;
      dur1 = (ub4)(cx >> Durshift) & Durlim;
      infocc(dbg,Notty,"  ~e1 %2u dur %u at \ad%u",e1+1,dur1,dift+gt0);
      if (dur1 + dift >= t2) break;

      t1 = dift;
      e1++;
    }
    infocc(dbg,Notty,"  e1 %2u dur %u at \ad%u",e1,dur1,t1+gt0);
    if (t1 + dur1 > t2) continue;

    infocc(dbg,Notty,"  e1 %2u dur %u at \ad%u",e1,dur1,t1+gt0);

    tx = t2 - (t1 + dur1);
    if (tx < lotx) lotx = tx;
    if (tx > hitx) hitx = tx;
  }
  if (lotx > 1000) info(Iter,"hop %u-%u lotx %u hitx %u evs %u,%u",hop1,hop2,lotx,hitx,evcnt1,evcnt2);

  *phitx = hitx;
  return lotx;
}

static ub8 rndx = 0x05a3ae52de3bbf0aULL;

// wikipedia xorshift 64*
static inline ub8 lrnd(void)
{
  rndx ^= rndx >> 12; // a
  rndx ^= rndx << 25; // b
  rndx ^= rndx >> 27; // c
  return (rndx * 2685821657736338717ULL);
}

static inline ub4 locate(ub8 *ev,ub4 evcnt,ub4 tf,ub4 *pei,ub8 *px)
{
  ub8 x;
  ub4 t;
  ub4 ei = *pei;

  do {
    x = ev[ei];
    t = x & Timlim;
  } while(t < tf && ++ei < evcnt);
  *pei = ei;
  *px = x;
  return t;
}

/* get a typical total duration between two hops based on a set of random samples
   returns #samples
 */
static ub8 estdurcnt,noest1,noest2;

static ub4 estdur2(lnet *net,ub4 hop1,ub4 hop2,ub4 dttmin,ub4 *pdtlo,ub4 *pdthi,ub4 *ptypdt)
{
  ub4 chopcnt = net->chopcnt;
  struct chop *hp1,*hp2,*hops = net->chops;
  ub8 x1,x2,*ev1,*ev2,*events = net->cevents;
  ub4 evcnt1,evcnt2;
  ub4 t1,t2,t22,dur1,dur2,dt,prvt1,prvt2,t2e,t1b;
  ub4 dtndx,dtcnt = 0;
  ub4 gt0 = net->t0;

  ub4 dts[Subsamples2];
  ub4 dtmax = Elemcnt(dts);

  ub4 dthibin = Est_statlen - 1;

  error_ge(hop1,chopcnt);
  error_ge(hop2,chopcnt);

  hp1 = hops + hop1;
  hp2 = hops + hop2;
  error_eq(hp1->kind,Taxi);
  error_eq(hp2->kind,Taxi);

  ev1 = events + hp1->evofs;
  ev2 = events + hp2->evofs;

  evcnt1 = hp1->evcnt;
  evcnt2 = hp2->evcnt;
  error_z(evcnt1,hop1);
  error_z(evcnt2,hop2);

  // if ( (estdurcnt++ % 100000) == 0) info(Noiter,"estdur2 \ah%lu %lu \ah%lu",estdurcnt,noest1,noest2);

  ub4 t10 = max(gst0,hp1->t0 - gt0);
  ub4 t11 = min(gst1,hp1->t1 - gt0);
  if (t11 <= t10) { noest1++; return 0; }

  ub4 ei1 = 0,ei2 = 0;

  ub4 ttmin = getmintt(globs.mintts,hp1->kind,hp2->kind);

  ttmin += dttmin;  // adjusted for preceding walk link

  ub4 nsamp = min(Subsamples,evcnt1);
  ub4 rndiv = max((t11 - t10) / nsamp,1);
  if (nsamp == 1) {
    t11 = t10 + 1;
    rndiv = 1;
  }

  t1 = t10;

  ub4 dtlo = hi32;
  ub4 dthi = 0;
  ub4 dtsum = 0;

  while (t1 < t11 && ei1 < evcnt1) {
    prvt1 = t1;
    t1 = locate(ev1,evcnt1,t1,&ei1,&x1);

    if (t1 < prvt1 || ei2 >= evcnt2) break;

    dur1 = (x1 >> Durshift) & Durlim;
    t2 = t1 + dur1 + ttmin;

    prvt2 = t2;
    t2 = locate(ev2,evcnt2,t2,&ei2,&x2);
    if (t2 < prvt2) break;
    dur2 = (x2 >> Durshift) & Durlim;
    t2e = t2 + dur2;

    // search for later start
    if (t2 - prvt2 > 5 && ei1 < evcnt1) {
      t1b = locate(ev1,evcnt1,t2 - ttmin,&ei1,&x1);
    }

    dtlo = min(dtlo,t2e - t1);
    dtsum += t2e - t1;

    dthi = max(dthi,t2e - prvt1);
    dtcnt++;

    t1 += (lrnd() % rndiv);
  }

  if (dtcnt == 0) { noest2++; return 0; }
  *pdtlo = dtlo;
  *pdthi = dthi;
  *ptypdt = dtsum / dtcnt;
  return dtcnt;
}

// get an average total duration between 3 hops
// based on a prepared handful of random samples
static ub4 estdur3(lnet *net,ub4 hop1,ub4 hop2,ub4 hop3,ub4 tt1min,ub4 tt2min,ub4 *pdtlo,ub4 *pdthi,ub4 *ptypdt)
{
#if 1
  return estdur2(net,hop1,hop2,tt1min,pdtlo,pdthi,ptypdt);  // placeholder
#else

  ub4 tdur1,tdur2,tdur3,*sev1,*sev2,*sev3,*sevents = net->sevents;
  ub4 scnt1,scnt2,scnt3,*sevcnts = net->sevcnts;
  ub4 e1,e2,e3;
  ub4 evcnt1,evcnt2,evcnt3;
  ub4 t1,t2,t3,dur1,dur2,dur3,dt;
  ub4 dtndx,dtcnt = 0;
  ub4 typdur;

  struct chop *chp1,*chp2,*chp3,*chops = net->chops;
  ub8 cx1,cx2,cx3,*cev1,*cev2,*cev3,*cevents = net->cevents;
  ub4 timlim = (1 << Durshift) - 1;
  ub4 dts[Subsamples2];
  ub4 dtmax = Elemcnt(dts);
  ub4 gt0 = net->t0;

  ub8 *sp = stat3_nocnt + tid * Escnt;
  ub4 *bp = dtbins3 + tid * Est_statlen;

  ub4 dthibin = Est_statlen - 1;
  ub4 msgtid = (tid << Tidshift) | Tidbit;
  int dbg = (opt & Est_dbg);

  error_zp(sevents,0);

  chp1 = chops + hop1;
  chp2 = chops + hop2;
  chp3 = chops + hop3;

  evcnt1 = chp1->evcnt;
  evcnt2 = chp2->evcnt;
  evcnt3 = chp3->evcnt;

  if (evcnt1 < minevcnt || evcnt2 < minevcnt || evcnt3 < minevcnt) { sp[H123c]++; return hi32; }

  scnt1 = sevcnts[hop1];
  scnt2 = sevcnts[hop2];
  scnt3 = sevcnts[hop3];

  cev1 = cevents + chp1->evofs;
  cev2 = cevents + chp2->evofs;
  cev3 = cevents + chp3->evofs;

  ub4 lodur1 = chp1->lodur;
  ub4 hidur1 = chp1->hidur;
  ub4 lodur2 = chp2->lodur;
  ub4 hidur2 = chp2->hidur;
  ub4 lodur3 = chp3->lodur;
  ub4 hidur3 = chp3->hidur;

  if (scnt1 && scnt1 <= scnt2 && scnt1 <= scnt3) {  // sample h1

    sev1 = sevents + hop1 * Subsamples;

    t2 = chp2->t0 - gt0;
    t3 = chp3->t0 - gt0;
    e2 = e3 = 0;

    cx2 = cev2[0];
    cx3 = cev3[0];
    dur2 = (ub4)(cx2 >> Durshift);
    dur3 = (ub4)(cx3 >> Durshift);
    error_lt(dur2,lodur2);
    error_lt(dur3,lodur3);
    error_gt(dur2,hidur2,hop2);
    error_gt(dur3,hidur3,hop3);

    for (e1 = 0; e1 < max(scnt1 / 3,Subsamples3) && dtcnt < dtmax; e1++) {
      tdur1 = sev1[e1];

      dur1 = tdur1 >> Durshift;
      t1 = (tdur1 & Timlim);

      // error_lt(dur1,lodur1);
      // error_gt(dur1,hidur1,hop1);

      // infocc(dbg,0,"e1 %u dur \at%u at \ad%u",e1,dur1,t1); // todo assess and remove
      while (e2 < evcnt2 && t2 < t1 + dur1 + tt1min) {
        cx2 = cev2[e2];
        // error_lt(dur2,lodur2);
        // error_gt(dur2,hidur2,hop2);
        t2 = (cx2 & timlim);
        e2++;
        // infocc(dbg,0,"e2 %u/%u at \ad%u",e2,evcnt2,t2);
      }
      if (t1 + dur1 + tt1min > t2) break;
      dur2 = (ub4)(cx2 >> Durshift);

      // infocc(dbg,0,"e2 %u/%u dur \at%u at \ad%u",e2,evcnt2,dur2,t2);

      while (e3 < evcnt3 && t3 < t2 + dur2 + tt2min) {
        cx3 = cev3[e3];
        dur3 = (ub4)(cx3 >> Durshift);
        // error_lt(dur3,lodur3);
        // error_gt(dur3,hidur3,hop3);
        t3 = (cx3 & timlim);
        e3++;
      }
      dur3 = (ub4)(cx3 >> Durshift);

      // infocc(dbg,0,"e3 %u/%u at \ad%u tt2min %u",e3,evcnt3,t3,tt2min);
      if (t2 + dur2 + tt2min > t3) break;
      // error_lt(t3,t1);
      dt = (t3 - t1) + dur3;
      dts[dtcnt] = dt;
      dtcnt++;
    }
    if (dtcnt == 0) sp[H1dt]++;
    sp[H1]++;
    infocc(dbg,msgtid|Notty,"h1 cnt %u",dtcnt);

  } else if (scnt2 && scnt2 < scnt1 && scnt2 <= scnt3) {  // sample h2

    sev2 = sevents + hop2 * Subsamples;

    e1 = e3 = 0;
    t1 = chp1->t0 - gt0;
    t3 = chp3->t0 - gt0;

    cx1 = cev1[0];
    cx3 = cev3[0];
    dur1 = (ub4)(cx1 >> Durshift);
    dur3 = (ub4)(cx3 >> Durshift);

    error_lt(dur1,lodur1);
    error_lt(dur3,lodur3);
    error_gt(dur1,hidur1,hop1);
    error_gt(dur3,hidur3,hop3);

    for (e2 = scnt2 / 3; e2 < (scnt2 * 2) / 3 && dtcnt < dtmax; e2++) {
      tdur2 = sev2[e2];

      t2 = (tdur2 & Timlim);

      if (t1 + dur1 + tt1min > t2) continue;

      dur2 = tdur2 >> Durshift;

      // error_lt(dur2,lodur2);
      // error_gt(dur2,hidur2,hop2);

      while (e1 + 1 < evcnt1) {
        cx1 = cev1[e1+1];
        dur1 = (ub4)(cx1 >> Durshift);
        // error_lt(dur1,lodur1);
        // error_gt(dur1,hidur1,hop1);
        if (dur1 + tt1min + (cx1 & timlim) >= t2) break;
        t1 = (cx1 & timlim);
        e1++;
      }

      if (t1 + dur1 + tt1min > t2) continue;

      while (e3 < evcnt3 && t3 < t2 + dur2 + tt2min) {
        cx3 = cev3[e3];
        dur3 = (ub4)(cx3 >> Durshift);
        // error_lt(dur3,lodur3);
        // error_gt(dur3,hidur3,hop3);
        t3 = (cx3 & timlim);
        e3++;
      }
      if (t2 + dur2 + tt2min > t3) continue;

      dur3 = (ub4)(cx3 >> Durshift);

      // error_lt(t3,t1);
      dt = (t3 - t1) + dur3;
      dts[dtcnt] = dt;
      dtcnt++;
    }
    if (dtcnt == 0) sp[H2dt]++;
    sp[H2]++;

  } else if (scnt3) {  // sample h3

    sev3 = sevents + hop3 * Subsamples;

    e1 = e2 = 0;
    t1 = chp1->t0 - gt0;
    t2 = chp2->t0 - gt0;

    cx1 = cev1[0];
    cx2 = cev2[0];
    dur1 = (ub4)(cx1 >> Durshift);
    dur2 = (ub4)(cx2 >> Durshift);

    error_lt(dur1,lodur1);
    error_lt(dur2,lodur2);
    error_gt(dur1,hidur1,hop1);
    error_gt(dur2,hidur2,hop2);

    for (e3 = (scnt3 * 2) / 3; e3 < scnt3 && dtcnt < dtmax; e3++) {
      tdur3 = sev3[e3];

      t3 = (tdur3 & Timlim);

      if (t2 + dur2 + tt2min > t3) continue;

      dur3 = (ub4)(tdur3 >> Durshift);

      // error_lt(dur3,lodur3);
      // error_gt(dur3,hidur3,hop3);

      while (e2 + 1 < evcnt2) {  // find best e2
        cx2 = cev2[e2+1];
        dur2 = (ub4)(cx2 >> Durshift);
        // error_lt(dur2,lodur2);
        // error_gt(dur2,hidur2,hop2);
        if (dur2 + tt2min + (cx2 & timlim) >= t3) break;
        t2 = cx2 & timlim;
        e2++;
      }

      if (t1 + dur1 + tt1min > t2) continue;

      while (e1 + 1 < evcnt1) {  // find best e1
        cx1 = cev1[e1+1];
        dur1 = (ub4)(cx1 >> Durshift);
        // error_lt(dur1,lodur1);
        // error_gt(dur1,hidur1,hop1);
        if (dur1 + tt1min + (cx1 & timlim) >= t2) break;
        t1 = cx1 & timlim;
        e1++;
      }

      // error_lt(t3,t1);
      dt = (t3 - t1) + dur3;
      dts[dtcnt] = dt;
      dtcnt++;
    }
    if (dtcnt == 0) sp[H3dt]++;
    sp[H3]++;

  } else { // original h1 forward
    t2 = chp2->t0 - gt0;
    t3 = chp3->t0 - gt0;
    e2 = e3 = 0;

    cx2 = cev2[0];
    cx3 = cev3[0];
    dur2 = (ub4)(cx2 >> Durshift);
    dur3 = (ub4)(cx3 >> Durshift);
    error_lt(dur2,lodur2);
    error_lt(dur3,lodur3);
    error_gt(dur2,hidur2,hop2);
    error_gt(dur3,hidur3,hop3);

    for (e1 = 0; e1 < scnt1 && dtcnt < dtmax; e1++) {
      cx1 = cev1[e1];
      dur1 = (ub4)(cx1 >> Durshift);
      t1 = cx2 & timlim;

      // error_lt(dur1,lodur1);
      // error_gt(dur1,hidur1,hop1);

      // infocc(dbg,0,"e1 %u dur \at%u at \ad%u",e1,dur1,t1); // todo assess and remove
      while (e2 < evcnt2 && t2 < t1 + dur1 + tt1min) {
        cx2 = cev2[e2];
        dur2 = (ub4)(cx2 >> Durshift);
        // error_lt(dur2,lodur2);
        // error_gt(dur2,hidur2,hop2);
        t2 = cx2 & timlim;
        e2++;
        // infocc(dbg,0,"e2 %u/%u at \ad%u",e2,evcnt2,t2);
      }
      if (t1 + dur1 + tt1min > t2) break;

      // infocc(dbg,0,"e2 %u/%u dur \at%u at \ad%u",e2,evcnt2,dur2,t2);

      while (e3 < evcnt3 && t3 < t2 + dur2 + tt2min) {
        cx3 = cev3[e3];
        dur3 = (ub4)(cx3 >> Durshift);
        // error_lt(dur3,lodur3);
        // error_gt(dur3,hidur3,hop3);
        t3 = cx3 & timlim;
        e3++;
      }
      // infocc(dbg,0,"e3 %u/%u at \ad%u tt2min %u",e3,evcnt3,t3,tt2min);
      if (t2 + dur2 + tt2min > t3) break;
      // error_lt(t3,t1);
      dt = (t3 - t1) + dur3;
      dts[dtcnt] = dt;
      dtcnt++;
    }
    if (dtcnt == 0) sp[H123dt]++;
    sp[H123]++;
  }

  switch (dtcnt) {
  case 0: // warn(0,"hop %u-%u-%u no estdur for evs %u-%u-%u,%u %s %s %s \ad%u \ad%u",
          //  hop1,hop2,hop3,evcnt1,evcnt2,evcnt3,scnt1,rp1->name,rp2->name,rp3->name,chp1->t0,chp2->t0);
          // info(Notty,"dir %d scnts %u,%u,%u dt %u,%u,%u",dir,scnt1,scnt2,scnt3,typdt1,typdt2,typdt3);
          return hi32;

  case 1: typdur = dts[0]; break;
  case 2: typdur = (dts[0] + dts[1]) / 2; break;
  case 3: typdur = (dts[0] + dts[1] + dts[2]) / 3;
    // warncc(typdur >= hi16,0,"%u,%u,%u for %u-%u-%u",dts[0],dts[1],dts[2],hop1,hop2,hop3);
    break;
  default: typdur = hi32; break;
  };
  if (typdur != hi32) {
    // warncc(typdur >= hi16,Exit,"typdur %u dtcnt %u for %u-%u-%u",typdur,dtcnt,hop1,hop2,hop3);
    bp[min(typdur,dthibin)]++;
    return typdur;
  }

  // take average except outliers
  ub4 lodt = hi32, hidt = 0;
  ub4 lodtcnt = 0,hidtcnt = 0;
  for (dtndx = 0; dtndx < dtcnt; dtndx++) {
    dt = dts[dtndx];
    if (dt < lodt) { lodt = dt; lodtcnt = 1; }
    else if (dt == lodt) lodtcnt++;
    if (dt > hidt) { hidt = dt; hidtcnt = 1; }
    else if (dt == hidt) hidtcnt++;
  }
  if (hidt == lodt || (hidt - lodt) * 10 < lodt) {
    bp[min(hidt,dthibin)]++;
    return hidt;
  }

  ub4 dtsum = 0,dtcnt2 = 0;
  for (dtndx = 0; dtndx < dtcnt; dtndx++) {
    dt = dts[dtndx];
    if ( (dt == lodt && lodtcnt * 8 < dtcnt) || (dt == hidt && hidtcnt * 8 < dtcnt) ) continue;
    dtsum += dt;
    dtcnt2++;
  }
  typdur = dtsum / max(dtcnt2,1);
  bp[min(typdur,dthibin)]++;

  return typdur;
#endif
}

ub4 estdur_3(lnet *net,ub4 h1,ub4 h2,ub4 h3,ub4 *pdtlo,ub4 *pdthi,ub4 *ptypdt)
{
  struct chop *chp1,*chp2,*chp3,*chops = net->chops;
  ub4 dur,dtcnt;
  ub4 chopcnt = net->chopcnt;
  ub4 whopcnt = net->whopcnt;
  // ub4 msgtid = (tid << Tidshift) | Tidbit;

  if (h1 >= whopcnt || h2 >= whopcnt || h3 >= whopcnt) return hi32;

  chp1 = chops + h1;
  chp2 = chops + h2;
  chp3 = chops + h3;
  int h1ev = (h1 < chopcnt && chp1->kind != Taxi);
  int h2ev = (h2 < chopcnt && chp2->kind != Taxi);
  int h3ev = (h3 < chopcnt && chp3->kind != Taxi);

  ub4 ttmin1 = getmintt(globs.mintts,chp1->kind,chp2->kind);
  ub4 ttmin2 = getmintt(globs.mintts,chp2->kind,chp3->kind);

  if (h1ev && h2ev && h3ev) {

    dtcnt = estdur3(net,h1,h2,h3,ttmin1,ttmin2,pdtlo,pdthi,ptypdt);
    dur = *ptypdt;
    // warncc(dur > hi16,msgtid,"dur %u ",dur);
    return dtcnt;

  } else if (h1ev && h2ev) {
    dtcnt = estdur2(net,h1,h2,0,pdtlo,pdthi,ptypdt);
    if (dtcnt) *ptypdt += chp3->lodur;
    // warncc(dur > hi16,msgtid,"dur %u ",dur);
    return dtcnt;
  } else if (h1ev && h3ev) {
    dtcnt = estdur2(net,h1,h3,chp2->lodur,pdtlo,pdthi,ptypdt);
    // warncc(dur > hi16,msgtid,"dur %u ",dur);
    return dtcnt;
  } else if (h2ev && h3ev) {
    dtcnt = estdur2(net,h2,h3,0,pdtlo,pdthi,ptypdt);
    if (dtcnt) *ptypdt += chp1->lodur;
    // warncc(dur > hi16,msgtid,"dur %u ",dur);
    return dtcnt;
  } else {
    dur = max(chp1->lodur + chp2->lodur + chp3->lodur,1);
    // warncc(dur > hi16,msgtid,"dur %u ",dur);
    *ptypdt = dur;
    return 1;
  }
}

ub4 estdur_2(lnet *net,ub4 h1,ub4 h2,ub4 *pdtlo,ub4 *pdthi,ub4 *ptypdt)
{
  ub4 typdt;
  struct chop *hp1,*hp2,*hops = net->chops;
  ub4 chopcnt = net->chopcnt;
  ub4 whopcnt = net->whopcnt;

  if (h1 >= whopcnt) {
    error(0,"invalid hop %u",h1);
    return 0;
  }
  if (h2 >= whopcnt) {
    error(0,"invalid hop %u",h1);
    return 0;
  }

  hp1 = hops + h1;
  hp2 = hops + h2;
  int h1ev = (h1 < chopcnt && hp1->kind != Taxi);
  int h2ev = (h2 < chopcnt && hp2->kind != Taxi);

  // infocc(dbg,0,"hop %u-%u lodur %u+%u %d %d",h1,h2,hp1->lodur,hp2->lodur,h1ev,h2ev);

  if (h1ev && h2ev) return estdur2(net,h1,h2,0,pdtlo,pdthi,ptypdt);

  typdt = max(hp1->lodur + hp2->lodur,1);
  *ptypdt = typdt;
  return 1;
}

// check whether two nonwalk hops have similar events in tdep and tarr
int dupevs(lnet *net,ub4 hop1,ub4 hop2)
{
  struct chop *hp1,*hp2,*hops = net->chops;
  ub4 e,nev1,nev2;

  hp1 = hops + hop1;
  hp2 = hops + hop2;
  if (hp1->kind == Taxi && hp2->kind == Taxi) {
    info(0,"rid %u taxi hop %u dups %u.%u",hp1->rid,hop1,hp2->rid,hop2);
    return 1;
  }
  else if (hp1->kind != hp2->kind) return 0;

  nev1 = hp1->evcnt;
  nev2 = hp2->evcnt;
  if (nev1 != nev2) return 0;
  if (hp1->t0 != hp2->t0) return 0;
  if (hp1->t1 != hp2->t1) return 0;
  if (hp1->srdep != hp2->srdep) return 0;
  if (hp1->srarr != hp2->srarr) return 0;

  ub8 cx1,cx2,*cev1,*cev2,*cevents = net->cevents;
  ub8 durtim = (1UL << (Durbits + Timbits)) - 1;

  cev1 = cevents + hp1->evofs;
  cev2 = cevents + hp2->evofs;

  for (e = 0; e < nev1; e++) {
    cx1 = cev1[e];
    cx2 = cev2[e];

    if ((cx1 & durtim) != (cx2 & durtim) ) break;
  }
  if (e < nev1) return 0;
  info(0,"rid %u hop %u dups %u.%u",hp1->rid,hop1,hp2->rid,hop2);
  return 1;
}
