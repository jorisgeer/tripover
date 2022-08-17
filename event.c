// event.c - time events like depart, arrive

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2015 Joris van der Geer.
 */

#include <string.h>

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

static const ub4 evlimit = 12 * 30 * 24 * 60;

// event sizes for fill pass
#define Dtidbits 14
#define Durbits  14
#define Srdabits 16

sassert(Dtidbits + Durbits + Srdabits + 1 < 63,"fill events < 64") sassert_end

static const ub4 durshift = Dtidbits + 1; // one bit to mark empty slot
static const ub4 srdashift = durshift + Durbits;

static const ub4 durlim = (1U << Durbits) - 1;
static const ub4 dtidlim = (1U << Dtidbits) - 1;

//#include "watch.h"

void inievent(int pass)
{
  static int passed;

  if (pass == 0 && passed == 0) {
    msgfile = setmsgfile(__FILE__);
    iniassert();
    passed = 1;
  } else if (pass == 1 && passed == 1) {
    passed = 2;
  }
}

/* merge services and time ranges for each route
 input is a list of gtfs-style entries like 'each wed dep 11.33 arr 11.36 valid 20140901-20141231'
 output is list of <time,trip> tuples over whole period.

 actual entry is tripid ( flightno in air) and duration
 times are in minutes UTC since Epoch

 expand for search and merged per dep,arr in netn
 */
void showxtime(struct timepatbase *tp,ub8 *xp,ub4 xlim)
{
  ub8 x;
  ub4 t,min,lmin;
  ub4 t0 = tp->t0, t1 = tp->t1;

  t = t0;
  error_ge(t1,xlim);

  while (t < t1) {
    x = xp[t];
    if (x == 0) { t++; continue; }

    min = t; // todo + tp->ht0;
    lmin = min2lmin(min,tp->utcofs);
    vrb(0,"hop %u \ad%u \ad%u tid %x",tp->hop,min,lmin,(ub4)(x & hi24));
    t++;
  }
}

// expand gtfs-style entries into a minute-time axis over validity range
// input and sid in localtime, events in utc
// returns number of unique departures
ub4 fillxtime(netbase *net,ub4 hop,struct timepatbase *tp,ub8 *xp,ub1 *xpacc,ub4 xlen,ub4 gt0,struct sidbase *sp,ub1 *daymap,ub4 tdeprep,ub4 repstart,ub4 repend,ub4 tid, const char *desc)
{
  struct hopbase *hp,*hops = net->hops;
  ub4 t,n = 0,ndup = 0;
  ub4 t00,t01,t0,t1,tt,tlo,thi,tday,t1day,mday,daycode;
  ub4 rsid = sp->rsid;
  ub4 rs6 = rsid & 0x3f;
  ub4 sid = sp->sid;
  ub4 utcofs = hp->utcofsd;
  ub4 maplen = sp->maplen;
  ub4 tdep,tdep0 = tdeprep & hi16;
  ub4 repiv = tdeprep >> 16;
  ub4 repcnt = 0;
  int dbg = 0;

  error_gt(repiv,1440 * 14,hop);
  warncc(repiv > 1440,0,"repiv %u",repiv);

  hp = hops + hop;
  t0 = sp->t0;
  t1 = sp->t1;  // exclusive

  t00 = sp->lt0day;
  t01 = sp->lt1day;

  error_zz(t0,t1);

  tlo = tp->t0; thi = tp->t1; // maintain actual range in reltime here

  error_lt(t0,gt0);
  error_lt(t0,gt0 + 1 * 1440 + 60); // max utcofs + dst
  error_lt(t1,gt0);

  error_nz(tid >> 24,tid);

  infocc(dbg,0,"r.sid %u.%u deptime %u t0 \ad%u t1 \ad%u t00 %u t01 %u",rsid,sid,tdep0,t0,t1,t00 * daymin,t01);
  infocc(dbg,0,"rep iv %u start \ad%u end \ad%u",repiv,tdep0,repend);

  if (tdep0 > daymin * 8) warning(Iter,"deptime > %u days",tdep0 / daymin);
//  if (tdep0 >= t1 - t0 + daymin) return warning(0,"hop %u deptime %u above schedule period \ad%u-\ad%u",hop,tdep0,t0,t1);

  if (tp->evcnt >= evlimit) return warning(0,"exceeding event limit %u %s",evlimit,desc);
  ub4 evlim = evlimit - tp->evcnt;

  tday = t00;
  t1day = t01;

  while (tday < t1day && n < evlim) {
    mday = tday - t00;
    error_ge(mday,maplen);

    daycode = daymap[mday];
    error_ne(rs6,daycode & 0x3f);

    if ((daycode & 0x80) == 0) { infocc(dbg,0,"no day at \ad%u",tday); tday++; continue; }
    else if (dbg) info(0,"day at %u",day2cd(tday));

    t = tday * daymin;

    if (repiv) {
      tdep = tdep0 + repstart;
    } else {
      repend = 0;
      tdep = tdep0;
    }

    repcnt = 0;
    do {
      tt = t - gt0 + tdep;
      if (tt >= xlen) {
        warning(0,"t %u tdep %u xlen %u n %u",t,tdep,xlen,n);
        return n;
      }
      ? if (tt < utcofs + 60) { tday++; continue; }
      tt = lmin2mini(tt,utcofs);
      ! if (daycode & 0x40) tt -= 60;  // dst in effect
      error_ge(tt,xlen);
      if ( (xp[tt] & hi32) == hi32) {
        xp[tt] = 0;
        tlo = min(tlo,tt);
        thi = max(thi,tt);
        n++;
        xpacc[tt >> Baccshift] = 1;
        // infocc(dbg && n < 20,Notty,"t \ad%u ",tt + gt0);
      } else {  // duplicate/overlap
        ndup++;
        // info(Iter|V0,"dup event at t %u \ad%u rsid %u %s",t,t,rsid,hops[hop].name);
      }
      tdep += repiv;
      // infocc(repiv > 1,0,"rep cnt %u iv %u end %u tdep %u",repcnt,repiv,repend,tdep);
      repcnt++;
    } while (tdep < tdep0 + repend && n < evlim);
    errorcc(repcnt > 1 && repiv == 0,0,"frq iv %u repeats %u",repiv,repcnt);
    tday++;
  }

  if (n) {
    if (n >= evlim) warning(Iter,"hop %u exceeding event limit %u",hop,evlimit);
    tp->t0 = tlo; tp->t1 = thi;   // keep track of first and last actual departure
    infocc(dbg,Notty,"hop %u t \ad%u - \ad%u %s",hop,tlo+gt0,thi+gt0,hops[hop].iname);
  } else if (ndup) info(Iter|V0,"%u dup events for rsid %u range %u-%u %s",ndup,rsid,tlo,thi,hp->name);
  else info(0,"no events for r.sid %u.%u range %u-%u",rsid,sid,t0,t1);
  infocc(dbg,0,"%u event\as, %u dup for r.sid %u.%u range %u-%u",n,ndup,rsid,sid,t0,t1);
  hp->dupevcnt += ndup;
  return n;
}

// similar to above, second pass after alloc
ub4 fillxtime2(struct timepatbase *tp,ub8 *xp,ub1 *xpacc,ub4 xlen,ub4 gt0,struct sidbase *sp,ub1 *daymap,ub4 maplen,ub4 tdeprep,ub4 repstart,ub4 repend,ub4 dtid,ub4 dur,ub4 srdep,ub4 srarr,ub4 evcnt)
{
  ub4 t,n = 0;
  ub4 t00,t01,t0,t1,tt,tday,t1day,mday;
  ub8 x;
  ub4 hop = tp->hop;
  ub4 utcofs = sp->utcofs;
  ub4 tdep,tdep0 = tdeprep & hi16;
  ub4 repiv = tdeprep >> 16;
  ub4 repcnt = 0;
  ub4 srda;
  int dbg = 0;

//  infocc(repiv > 1,0,"rep %u tdep %u end %u",repiv,tdep0,repend);
  error_gt(repiv,1440 * 14,hop);

  t0 = sp->t0;
  t1 = sp->t1;

  t00 = sp->lt0day;
  t01 = sp->lt1day;

  infocc(dbg,0,"rep iv %u start \ad%u end \ad%u",repiv,tdep0,repend);

//  if (tdep0 >= t1 - t0 + daymin) return warning(0,"hop %u deptime %u above schedule period \ad%u-\ad%u",hop,tdep0,t0,t1);

  srdep &= 0xff; srarr &= 0xff; srda = (srdep << 8) | srarr;

  t1day = t01;

  tday = t00;

  if (evcnt >= evlimit) return warning(0,"hop %u exceeding event limit %u",hop,evlimit);
  ub4 evlim = evlimit - evcnt;

  while (tday < t1day && n < evlim) {
    t = tday * daymin;
    mday = tday - t00;
    error_ge(mday,maplen);
    if ((daymap[mday] & 0x80) == 0) { tday++; continue; }

    if (repiv) {
      tdep = tdep0 + repstart;
    } else {
      repend = 0;
      tdep = tdep0;
    }

    repcnt = 0;
    do {
      tt = t - gt0 + tdep;
      if (tt >= xlen) return n;
      else if (tt < utcofs + 60) { tday++; continue; }

      tt = lmin2mini(tt,utcofs);
      if (daymap[mday] & 0x40) tt -= 60;  // dst in effect
      error_ge(tt,xlen);
      if ( (xp[tt] & hi32) == hi32) {
        x = (ub8)dtid;
        x |= (ub8)dur << durshift;
        x |= (ub8)srda << srdashift;
        xp[tt] = x;
        n++;
        xpacc[tt >> Baccshift] = 1;
      }
      tdep += repiv;
//      infocc(repiv > 1,0,"rep cnt %u iv %u end %u tdep %u",repcnt,repiv,repend,tdep);
      repcnt++;
    } while (tdep < tdep0 + repend && n < evlim);

    tday++;
  }
  infocc(n >= evlim,0,"%u + %u events at limit",n,tp->evcnt);
  infocc(dbg,0,"%u events range %u-%u",n,t0,t1);
  return n;
}

void clearxtime(struct timepatbase *tp,ub8 *xp,ub1 *xpacc,ub4 xlim)
{
  ub4 t,tt,t0,t1;

  t0 = tp->t0; t1 = tp->t1;

  t = t0;

  error_ge(t1,xlim);
  error_ge(t0,xlim);

  ub4 acc = 1 << Baccshift;
  tt = t >> Baccshift;
  t = tt << Baccshift;
  error_ge(t1,hi32 - acc);
  while (t <= t1) {
    if (xpacc[tt]) {
      memset(xp + t,0xff,acc * sizeof(*xp));
      xpacc[tt] = 0;
    }
    t += acc; tt++;
  }
}

// reduce events outside given period to about once daily
// and inside period to at most one per few minutes
ub4 filterxtime(struct timepatbase *tp,ub8 *xp,ub1 *xpacc,ub4 xlim,ub4 period0,ub4 period1)
{
  ub4 t0 = tp->t0;
  ub4 t1 = tp->t1; // keep actual range
  ub4 gt0 = tp->gt0;

  ub4 cnt = 0;

  ub4 t,rt = t0;
  ub4 prvrt = t0;
  ub8 x;

  ub4 acc = (1 << Baccshift);

  error_ge(t1,xlim);

  if (period0 == 0 && period1 == 0) return tp->evcnt;

  rt >>= Baccshift; rt <<= Baccshift;

  while (rt <= t1) {
    if (xpacc[rt >> Baccshift] == 0) { rt += acc; continue; }
    x = xp[rt];
    if ( (x & hi32) == hi32) { rt++; continue; }
    if (rt == t0 || rt == t1) { prvrt = rt++; cnt++; continue; }
    t = rt + gt0;
    if (t > period0 && t < period1) {
      if (cnt == 0 || rt - prvrt > 3) { prvrt = rt++; cnt++; continue; }
      xp[rt++] = hi64;
      continue;
    }
    error_lt(rt,prvrt);
    if (cnt == 0 || rt - prvrt >= 1440 * 2) { prvrt = rt++; cnt++; continue; }
    xp[rt++] = hi64;
  }
  infocc(cnt != tp->evcnt,Notty|Iter,"evcnt %u -> %u t \ad%u - \ad%u \ad%u \ad%u",tp->evcnt,cnt,t0+gt0,t1+gt0,period0,period1);

  return cnt;
}

// comparable to above, fill pass using info above
ub4 filltrep(netbase *net,struct chainbase *chbase,ub4 chaincnt,ub4 rid,block *evmem,struct timepatbase *tp,ub8 *xp,ub1 *xpacc,ub4 xlim)
{
  ub4 hop = tp->hop;
  ub4 t0,t1,t,gt0,prvt;
  ub4 tid,dtid;
  ub8 x;
  ub4 dur,prvdur,srda;
  ub8 *evs;
  ub4 gndx = 0;
  struct chainbase *chp;
  struct routebase *rp,*routes = net->routes;
  struct hopbase *hp,*hops = net->hops;
  int dbg = 0;
  int overtake = 0;

  evs = blkdata(evmem,tp->evofs,ub8);
  hp = hops + hop;

  t0 = tp->t0; t1 = tp->t1;
  gt0 = tp->gt0;

  error_ge(t1,xlim);
  rp = routes + rid;
  ub4 lochain = rp->lochain;
  ub4 chainpos = rp->chainpos;

  t = prvt = t0;
  prvdur = 0;

  ub4 tday0 = 0,cnt24 = 1,prv24 = 0;

  infovrb(dbg,0,"evcnt %u t \ad%u - \ad%u",tp->evcnt,t0+gt0,t1+gt0);

  t >>= Baccshift; t <<= Baccshift;
  while (t <= t1 && gndx < tp->evcnt * 2) { // todo <= ?
    if (xpacc[t >> Baccshift] == 0) { t += (1 << Baccshift); continue; }
    x = xp[t];
    if ( (x & hi32) == hi32) { t++; continue; }

    // count daymaps
    if (gndx == 0) tday0 = t;
    else if (t - tday0 < daymin) cnt24++;
    else {
      do tday0 += daymin; while (t - tday0 >= daymin);
      infocc(dbg,0,"cnt %u prv %u",cnt24,prv24);
      prv24 = cnt24;
      cnt24 = 1;
    }

    error_ge(gndx,tp->evcnt * 2);
    bound(evmem,gndx + 1,ub8);
    dur = (x >> durshift) & durlim;

    error_gt_cc(dur,1440 * 14,"hop %u dur \ax%u",hop,(ub4)dur);
    if (t + dur < prvt + prvdur) {
      infocc(overtake == 0 && prvt + prvdur - (t + dur) > 3,Iter|0,"hop %u t \ad%u dur %u overtakes \ad%u dur %u",hop,t + gt0,dur,prvt + gt0,prvdur);
      tp->overtakehi = max(tp->overtakehi,prvt + prvdur - (t + dur));
      overtake = 1;
    }
    prvt = t;
    prvdur = dur;
    dtid = x & dtidlim;
    error_ge(dtid,chainpos);
    tid = dtid + lochain;
    error_ge(tid,chaincnt);
    chp = chbase + tid;
    error_ne(chp->rid,rid);
    error_ge(dtid,hi16);
    srda = (x >> srdashift) & hi16;
    error_ge(t,hi32);

    evs[gndx++] = ((ub8)dur << 32) | t;

    x = ((ub8)srda << 32) | ( (hop & hi16) << 16) | dtid;
    evs[gndx++] = x;  // srdep.8 srarr.8 dtid.32 dur.32 t.32
    // infocc(hop == 0 && gndx == 2,0,"x %lx at %p",x,evs);
    // infocc(hop == 0,Iter,"t %u dur %lu dtid %u",t,dur,dtid);
    t++;
  }
  tp->overtake = overtake;
  vrb0(0,"hop %u fill %u events",hop,gndx / 2);
  return gndx / 2;
}
