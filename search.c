// search.e - core trip planning

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2017 Joris van der Geer.
 */

/* perform the actual trip search.

   see Transit directions at global scale, Jan 2016'  http://arxiv.org/abs/1601.03633
 */

// !start

#include <string.h>

#include "base.h"
#include "cfg.h"
#include "mem.h"
#include "time.h"
#include "math.h"
#include "util.h"
#include "os.h"

static ub4 msgfile;
#include "msg.h"

#include "iadr.h"
#include "net.h"

#undef hdrstop

#ifdef __clang__
 #pragma clang diagnostic ignored "-Wunused-variable"
 #pragma clang diagnostic ignored "-Wunreachable-code"
#endif

#ifdef __GNUC__
 #pragma GCC diagnostic ignored "-Wunused-variable"
#endif

// set to nonzero to include tracking, 0 for production
#define Track 0

#include "search.h"

// max number of vias in dyn1
#define Dyn1_midlim 4096

// max number of vias in dyn2
#define Dyn2_midlim 2048

// max number of vias in dyn3
#define Dyn3_mid1lim 4096
#define Dyn3_midlim 1024

static const ub4 altlimit2 = 1024 * 8; // todo
static const ub4 var1lim2 = 256;

static const ub4 altlimit3 = 1024 * 2;

// aimed number of departures for auto departure timespan
static const ub4 autodepdy = 3;
static const ub4 autodephr = 3;
static const ub4 autodepmax0 = 4 * 20 * 3;

static bool time_virtual = 0;

static const ub4 Maxevs = 4 * 1024;

static int vrbena;

static const char plancfgname[] = "plan";

struct srcplan {
  ub4 ndx;
  ub4 nleg1,nleg2,nleg3,nleg4; // designates dynx search on netn net
  ub4 tlim;                    //  scaled time to run
  ub4 tuse;                    //  scaled max spare time
  ub4 p0,p1;
  ub4 sort;
  ub4 run;
  ub4 cost;
};

// as above, init version
struct csrcplan {
  ub4 nleg1,nleg2,nleg3,nleg4;
  ub4 tlim;
  ub4 tuse,sort;
};

static struct srcplan plan3[Planlen];
static struct srcplan plan2[Planlen];
static struct srcplan plan1[Planlen];
static struct srcplan plan0[Planlen];

enum evfld {
 timefld,
 tidfld,
 durfld,
 sdurfld,
 costfld,
 prvfld,
 farefld,
 sdafld,
#if Track
  flnfld,
#endif
 fldcnt
};

static ub4 costleads[6 << 9];

static const ub2 evmagic1 = 0xbdc9;
static const ub2 evmagic2 = 0x695c;

static struct srcnet {
  struct network *net;
  ub4 portcnt;
} sn;

static ub8 gstat_evcnt,gstat_lkcnt;

void inisrc(gnet *net,search *src,const char *desc,ub4 arg)
{
  ub4 i,leg,t;
  ub2 *ev,*evbase;
  struct trip *stp;
  ub4 portcnt = net->portcnt;

  sn.net = net;

  error_ovf(Maxevs,ub2);

  fmtstring(src->desc,"%s %u",desc,arg);

  src->costlim = hi32;
  src->lodist = hi32;
  src->lodt = hi32;
  src->reslen = 0;
  src->ntrip = 0;

  src->de_prvhop = hi32;

  for (t = 0; t < Elemcnt(src->trips); t++) {
    stp = src->trips + t;
    stp->len = 0;
    stp->cost = hi32;
    for (i = 0; i < Nleg; i++) {
      stp->trip[i] = hi32;
      stp->port[i] = hi32;
    }
  }

#if 0
  if (src->evpool == NULL) {
    info(0,"alloc new %u event pool",Maxevs);
    evbase = src->evpool = alloc(Nleg * (Maxevs + 2) * fldcnt,ub2,0,"src events",Maxevs);
  } else evbase = src->evpool;
  ev = evbase;
  for (leg = 0; leg < Nleg; leg++) { // add a redzone around each leg
    ev = evbase + leg * (Maxevs + 2) * fldcnt;
    *ev = evmagic1;
    src->depevs[leg] = ev + fldcnt;
    ev += (Maxevs + 1) * fldcnt;
    *ev = evmagic2;
  }
  if (ev >= evbase + Nleg * (Maxevs + 2) * fldcnt) error(Exit,"ev %p above %p",(void *)ev,(void *)(evbase + Nleg * (Maxevs + 2) * fldcnt));
#endif

  if (src->infconns) return;

  src->infconns = alloc(portcnt,ub1,0,"src infcon",0);
  src->infdaconns = alloc(portcnt * Nleg,ub4,0,"src infcon",0);
}

static void timelimit(search *src,ub4 slimit,const char *desc,int rel)
{
  ub4 limit = max(slimit,1);
  ub8 t1 = limit;

  if (rel) t1 += gettime_msec();
  else t1 += src->queryt0;

  vrb0(0,"set timeout at %u * %u = %u msec for %s",slimit,src->limitfac,limit,desc);
  src->querytlim = t1;
  src->tlim = limit;
  src->limitdesc = desc;
}

static int timeout(ub4 fln,search *src,struct srcplan *sp,ub4 arg1,ub4 arg2)
{
  if (isalarm() == 0) return 0;

  infofln(fln,0,"src.%u timeout at %u ms %u/%u",__LINE__,src->tlim,arg1,arg2);

  src->tlim = 0;
  if (sp) {
    sp->p0 = arg1;
    sp->p1 = arg2;
  }
  return 1;
}

static void fmtsum(ub4 fln,struct trip *stp,ub4 dt,ub4 nxt,ub4 dist,ub4 fare,ub4 lodt,const char *ref)
{
  ub4 len = (ub4)sizeof(stp->desc);
  ub4 pos = mysnprintf0(stp->desc,0,len,"#item\ttime\tdistance\tstops\tfare\tref\n");

  if (nxt == 0) nxt = hi32;
  pos += mysnprintf(stp->desc,pos,len,"sum\t\at%u\t\ag%u\t%u\t%u\t\at%u\t%s-%u-%u\n",dt,dist,stp->len - 1,fare,nxt,ref,fln & hi16,lodt);
  stp->desclen = pos;
}

// heuristic limit for over-route versus direct
static ub4 geodistlim(ub4 dir)
{
  if (dir < 100) return dir * 8;
  else if (dir < 1000) return dir * 7;
  else if (dir < 10000) return dir * 6;
  else if (dir < 100000) return dir * 5;
  else if (dir < 500000) return dir * 4;
  else return dir * 3;
}

// geographical direct line distance from grid or direct
static ub4 xgeodist(struct port *pdep,struct port *parr,ub4 seqdep,ub8 gseqcnt,ub2 *seqdist)
{
  ub4 dir;

  if (seqdist && (pdep->gridlat + 1 < parr->gridlat || pdep->gridlon + 1 < parr->gridlon
    || parr->gridlat + 1 < pdep->gridlat || parr->gridlon + 1 < pdep->gridlon) ) {
    dir = (ub4)seqdist[(ub8)seqdep * gseqcnt + parr->gridseq] << Gridshift;
  } else dir = fgeodist(pdep,parr,1);
  return dir;
}

static int chkdev(ub2 *dev,ub4 leg)
{
  if (dev == NULL) return errorfln(FLN,0,0,"leg %u nil dev",leg);

  ub2 *d1 = dev - fldcnt;
  ub2 *d2 = dev + Maxevs * fldcnt;

  if (*d1 != evmagic1) return errorfln(FLN,0,0,"leg %u magic1 mismatch %x at %p",leg,*d1,(void *)d1);
  else if (*d2 != evmagic2) return errorfln(FLN,0,0,"leg %u magic2 mismatch %x at %p",leg,*d2,(void *)d2);
  else return 0;
}

#if 0
// get suitable departure window given ev frequency
// based on leg with lowest frequency around deptime
static ub4 getdepwin(search *src,lnet *net,ub4 *legs,ub4 nleg)
{
  ub4 deptmin = src->deptmin;
//  ub4 winmax = src->deptmin;
  ub4 gt0 = net->t0;
  ub4 hrt0,rt0 = deptmin - gt0;
  ub1 *covhrp,*covhr = net->covhr;
  ub2 *covdyp,*covdyp0,*covdy = net->covdy;
  ub8 rnghr = net->rnghr;
  ub4 rngdy = net->rngdy;
  ub4 leg,hop;
  struct chop *hp,*hp0,*hops = net->chops;
  ub1 *modes = net->hopmodes;
  ub4 chopcnt = net->chopcnt;
  ub4 depwin,hidepwin = 0,hidhleg = 0;
  ub4 days,hours,sumhr,sumdy,sumdy0;
  ub4 covdyndx,covdyndx0,covhrndx,covdy0,covhr0;

  error_z(nleg,0);

  hop = legs[0];
  for (leg = 0; leg < nleg; leg++) {
    hop = legs[leg];
    if (hop < chopcnt && modes[hop] != Taxibit) break;
  }

  hp0 = hops + hop;
  covdyp0 = covdy + hp0->mapofsdy;

  hrt0 = rt0;
  for (leg = 0; leg < nleg; leg++) {
    hop = legs[leg];
    hp = hops + hop;
    if (hop >= chopcnt || modes[hop] == Taxibit) { // walk/taxi link
      hrt0 += hp->lodur;
      continue;
    }

    covhrp = covhr + hp->mapofshr;
    covdyp = covdy + hp->mapofsdy;

    covhrndx = covhr0 = hrt0 / 60;
    covdyndx = covdy0 = covhr0 / 24;

    // count days until desired min #events reached, limited by leg0 events
    sumdy = sumhr = sumdy0 = 0;
    covdyndx0 = rt0 / 60;
    covdyndx0 /= 24;
    while (sumdy < autodepdy && covdyndx < rngdy && covdyndx0 < rngdy && sumdy0 < autodepmax0) {
      sumdy += covdyp[covdyndx++];
      sumdy0 += covdyp0[covdyndx0++];
    }
    while (sumdy == 0 && covdyndx < rngdy) sumdy += covdyp[covdyndx++];

    days = covdyndx - covdy0;
    if (days > 2) {
      depwin = days * 24 + 12;
      if (depwin > hidepwin) {
        hidepwin = depwin;
        hidhleg = leg | (days << 8);
      }

      // infocc(dbg,Noiter,"hop %u days %u dycnt %u evs %u at \ad%u",hop,days,sumdy,hp->evcnt,hrt0 + gt0);
      hrt0 += hp->lodur;
      continue;
    }
    while (sumhr < autodephr && covhrndx < rnghr) sumhr += covhrp[covhrndx++];

    hours = covhrndx - covhr0;
    // infocc(dbg,Noiter,"hop %u days %u cnt %u hours %u cnt %u evs %u at \ad%u",hop,days,sumdy,hours,sumhr,hp->evcnt,hrt0 + gt0);
    depwin = hours;
    if (depwin > hidepwin) {
      hidepwin = depwin;
      hidhleg = leg | (days << 8) | (hours << 16);
    }

    hrt0 += hp->lodur;
  }
  leg = hidhleg & 0xff;
  hop = legs[leg];
  src->dwleg = leg;
  src->dwhop = hop;
  src->dwday = (hidhleg >> 8) & 0xff;
  src->dwhr = hidhleg >> 16;

  return hidepwin + 1;
}
#endif

#if Track
 #define track(d,v) (d)[flnfld] = (v)
#else
 #define track(d,v)
#endif

#define Hitime(dt,df) (ub2)((dt) + ((df) >> 4))
#define Hifare(dt,df) (ub2)((df) + ((dt) >> 4))

#if 0
// example
%generate mode=Srclotime,Srchitime dofare=0,1
static ub4 mkdepevs(search *src,lnet *net,ub4 hop,ub4 costlim,int dbg)
{
  ub4 deptmin = src->deptmin;

%mode=Srchitime cost = hitime
  x
%mode=Srclotime cost = lotime
  y
%dofare=1  cost += fare

}

  rv = mkdepevs(%mode,%dofare,a,b,c) && return 1;

#endif
// %line

/*
 step 1:
 search first few evs for each leg, using first ev or preceding leg and lodur + mintt

 step 2:
 starting from lowest freq:
   for each previous leg, for each ev fill about 5 preceding evs with basic info
   for each next leg, for each ev fill about 5 preceding evs with basic info


 step 3
   compose trips and assign cost

 step 4
   if not enough trips, extend more: step 2


 no sdeparr offsets: consider only smaller grouplimit

  depwin : user specifies travel window, possibly including arrival window
           use events outside window if none within and curcost high
  src effort level and curcost determine #events to consider
  autodep no longer sensible : default flexdays to 3 ?

  'metro mode' if span equal and short : forward only
 */

// get first handful of evs in depwin, report timespan. store tentatively

#if 0

/* find tf start pos
   daymap : ofs 36  64 bits
   50m chops * 200d = 80gb
   acc 6b next day 6b next week
       index into hop[warptab]
 */

#define hrwarp 60

// struct chop *hp,ub4 tf,ub4 t,ub4 ei,ub8 x
%expand locate(net,hp,tf,t,ei,x)
{
 {
  ub4 tofs;
  ub8 dx,*dmp = net->daymap + hp->dayofs;
  ub4 evcnt = hp->evcnt;
  ub4 zei,dayno;
  const ub4 day = 1440;
  const ub8 rel = 1UL << 63;
  ub8 *ev = net->cevents + hp->evofs;

  error_ge(ei,evcnt);
  x = ev[ei];
  t = x & Timlim;
  if (hp->haveacc) {
    while(ei < evcnt && t < tf) {
      if (tf - t >= day) {
        ei += x;  /* dywarp */
      } else if (x) { /* rel */
        dayno = x;   /* dur */
        dx = dmp[dayno];
        zei = net->reltab[dx]; /* ofs */
        tofs = dx; /* tofs */
        do {
          if (tf - t >= hrwarp) {
            zei += 1; /* x.hrwarp; */
          }
          x = ev[zei];
          t = x & Timlim;
          t += tofs;
        } while( (x & rel) && t < tf);

      } else {
        if (tf - t >= hrwarp) {
          ei += x;  /* hrwarp */
        }
        x = ev[++ei];
        t = x & Timlim;
      }
    }

  } else { /* no acc -> no compress */
    do {
      x = ev[ei];
      t = x & Timlim;
    } while(t < tf && ++ei < evcnt);
  }
 }
}
#endif

#if 0
struct evsrc {
  ub4 span;
  ub4 ts[Nsrcev];
  ub4 durs[Nsrcev];
};

// find first few evs from given start. return first
static ub4 firstevs(search *src,ub4 leg,struct chop *hp,ub4 t0,struct evsrc *ep)
{
  ub4 lodur = hp->lodur;
  ub4 t,tf;
  ub4 span;

  locate(tday0,dt,t,gndx,cnt24)

  span = t - tf;
  ep->span = span;
  return tf;
}

#define Nsrcev 16

static ub4 evalevs(search *src,ub4 *legs,ub4 nleg,ub4 costlim,ub4 *ts,ub4 *durs)
{

}

static ub4 srcevs(search *src,lnet *net,ub4 *legs,ub4 nleg,ub4 costlim)
{
  struct chop *hp,*ahp,*hops = net->chops;
  ub4 deptmin = src->deptmin;
  ub4 *mintts = src->mintts;
  ub4 gt0 = net->t0;
  ub4 t0 = deptmin - gt0;
  struct evsrc evsrcs[Nleg];
  struct evsrc *ep;

  ub4 leg,h;
  ub4 dur;

  ub4 tf = t0;

  ahp = hops + legs[0];
  for (leg = 0; leg < nleg; leg++) {
    h = legs[leg];
    ahp = hp;
    hp = hops + h;
    ep = evsrcs + leg;
    if (hp->hasfrq) {
      tf = firstevs(src,leg,hp,tf,ep);
      tf += getmintt(mintts,ahp->kind,hp->kind);
    } else tf += hp->lodur;

    span = ep->span;
    if (span > hispan) {
      hispan = span; hileg = leg;
    }
    if (span < lospan) {
      lospan = span; loleg = leg;
    }
  }
  if (lospan * 2 > hispan) { // comparable freqs: no need to fill
    return evalevs(src,net,nleg,evsrcs);
  }

  do {
    while (hileg) {
      span = bckevs(src,hileg,costlim);
      hileg--;
    }
    while (hileg < nleg1) {
      span = fwdevs(src,hileg,costlim);
      hileg++;
    }
    evalevs(src,net,nleg,evsrcs);
  } while (dcnt < 4);

/*

 */

  return 0;
}
#else

static ub4 gs_useacc;

static ub4 locate_acc(ub4 fln,struct route *rp,ub8 *ev,ub4 evcnt,ub4 tf,ub4 *pei,ub8 *px,ub8 *pprvx)
{
  ub8 prvx,x;
  ub4 t;
  ub4 acc,iacc;
  ub4 ei = 0;
  ub2 *acc1tab = rp->acc1tab;
  ub4 acc1len = rp->acc1len;

  x = prvx = ev[0];
  t = x & Timlim;

  if (tf <= t) {
    *pei = 0;
    *px = x;
    *pprvx = 0;
    return t;
  }

  while (t + Acc1iv < tf) {
    acc = (x >> Acc1shift) & Acc1lim;
    // if (acc >= acc1len) fatalfln(FLN,0,fln,"rid %u ev %u/%u acc %u ge %u",rp->rid,ei,evcnt,acc,acc1len);
    iacc = acc1tab[acc];
    ei += iacc;
    if (ei >= evcnt) break;
    x = ev[ei];
    t = x & Timlim;
  }

  while (t < tf && ei + 1 < evcnt) {
    x = ev[++ei];
    t = x & Timlim;
  }
  if (ei >= evcnt) {
    prvx = ev[evcnt - 1];
    t = prvx & Timlim;
  } else if (ei) prvx = ev[ei-1];
  *pprvx = prvx;
  *px = x;
  return t;
}

// return first time and pos at or after tf. caller checks range
static ub4 locate(ub4 fln,struct route *rp,ub8 *ev,ub4 evcnt,ub4 tf,ub4 *pei,ub8 *px,ub8 *pprvx)
{
  ub8 prvx,x;
  ub4 t;
  ub4 ei;

  if (gs_useacc) return locate_acc(fln,rp,ev,evcnt,tf,pei,px,pprvx);

  ei = 0;
  gstat_lkcnt++;
  x = ev[0];

  do {
    prvx = x;
    x = ev[ei];
    t = x & Timlim;
  } while(t < tf && ++ei < evcnt);
  gstat_evcnt += ei;
  *px = x;
  *pprvx = prvx;
  *pei = ei;
  return t;
}

static ub4 getres(search *src,lnet *net)
{
  struct chop *hp,*hops = net->chops;
  ub4 altpos = src->altpos;
  ub4 chopcnt = net->chopcnt;
  struct srcres *rp = src->curres + altpos;
  struct srcxres *xp = src->curxres + altpos;
  struct trip *tp = src->trips;
  struct route *rtp,*routes = net->routes;
  ub4 h,l,nleg,*legs;
  ub4 evcnt,ei;
  ub4 t,prvt,td;
  ub4 rid;
  ub4 gt0 = net->t0;
  ub4 gt1 = net->t1;
  ub4 dur;
  ub4 dtid,tid;
  ub2 srda,srdep,srarr;
  ub2 *srdap,*srdalst = net->evsrdas;
  ub8 x,prvx,*ev,*events = net->cevents;
  ub4 cost = src->costlim;

  info(0,"getres pos %u d%u %u-%u-%u-%u %u-%u cost %u",altpos,xp->ndyn,xp->nleg0,xp->nleg1,xp->nleg2,xp->nleg3,xp->i0,xp->i1,cost);

  nleg = rp->nleg;
  if (nleg == 0) return warn(0,"nil result for pos %u",altpos);
  t = rp->td[0];
  for (l = 0; l < nleg; l++) {
    h = rp->hop[l];
    prvt = t;
    t = rp->td[l];
    if (t == 0) return hopmsg(Warn,0,h,"leg %u/%u rt 0 at \ad%u",l,nleg,gt0);
    else if (t > gt1) return hopmsg(Warn,0,h,"leg %u/%u rt %u above \ad%u",l,nleg,t,gt1);
    else if (t < prvt) return hopmsg(Warn,0,h,"leg %u/%u t %u before %u \ad%u < \ad%u",l,nleg,t,prvt,t + gt0,prvt + gt0);
    hp = hops + h;
    if (h < chopcnt) {
      rtp = routes + hp->rid;
      ev = events + hp->evofs;
      evcnt = hp->evcnt;
      td = locate(FLN,rtp,ev,evcnt,t,&ei,&x,&prvx);
      if (td != t) return hopmsg(Warn,0,h,"t \ad%u not found at leg %u: \ad%u",t + gt0,l,td + gt0);
    } else {
      td = t;
      ei = 0;
      x = rp->x[l];
    }
    rid = hp->rid;
    if (rid >= net->ridcnt) hopmsg(Warn,0,h,"leg %u has invalid rid %u",l,rid);
    rtp = routes + rid;
    dur = (x >> Durshift) & Durlim;
    dtid = (x >> Dtidshift) & Dtidlim;

    tid = rtp->lochain + dtid;
    if (h < chopcnt && tid >= rtp->hichain) hopmsg(Warn,0,h,"leg %u rid %u has invalid tid %u above %u, dtid 0x%x",l,rid,tid,rtp->hichain,dtid);
    if (hp->varsda) {
      srdap = srdalst + hp->sdaofs;
      srda = srdap[ei];
      srdep = srda >> 8;
      srarr = srda & 0xff;
    } else {
      srdep = hp->srdep;
      srarr = hp->srarr;
    }
    tp->trip[l] = h;
    tp->dur[l] = dur;
    tp->t[l] = t + gt0;
    tp->tid[l] = tid;
    tp->srdep[l] = (srdep == 0xff ? hi16 : srdep);
    tp->srarr[l] = (srarr == 0xff ? hi16 : srarr);
  }
  tp->len = nleg;
  src->ntrip = 1;
  return 1;
}

static ub4 srcevs1(ub4 fln,search *src,lnet *net,ub4 h,ub4 costlim)
{
  struct chop *hp,*prvhp,*hops = net->chops;
  struct port *pdep,*ports = net->ports;
  struct route *rtp,*routes = net->routes;
  ub4 chopcnt = net->chopcnt;
  ub4 deptmin = src->deptmin;
  ub4 deptmax = src->deptmax;

  ub8 x1,x2,prvx,*ev,*ev2,*events = net->cevents;

  struct srcres *rp,*res = src->res;

  ub4 evcnt,evcnt2,l,prvh;
  ub4 t1,t2,t22,dur,dur2,dt,prvt1,prvt2,t2e,t1b;
  ub4 tdep,tarr,cost;
  ub4 dtndx,dtcnt = 0;
  ub4 gt0 = net->t0;

  ub4 th,tf = deptmin - gt0;

  ub4 ei1 = 0,ei2 = 0;

  ub4 td = 0,ta;
  ub4 eiarr,ei = 0;
  ub4 rescnt,ri = 0;

  ub8 x;

  if (h >= chopcnt) { errorfln(FLN,0,fln,"leg 0 hop %u >= %u",h,chopcnt); return costlim; }
  hp = hops + h;

  evcnt = hp->evcnt;
  if (evcnt == 0) return costlim;
  rtp = routes + hp->rid;
  ev = events + hp->evofs;

  rp = res;
  tdep = locate(FLN,rtp,ev,evcnt,tf,&ei,&x,&prvx);
  if (tdep < tf) return costlim;
  rp->td[0] = tdep;
  rp->hop[0] = h;
  dur = (x >> Durshift) & Durlim;
  ta = tdep + dur;

  cost = ta - tdep;
  if (cost >= costlim) return costlim;

  rp->cost = cost;
  rp->nleg = 1;
  src->locost = cost;
  src->lores = 0;
  src->rescnt = ri;
  return cost;
}

static ub4 srcevs(ub4 fln,search *src,lnet *net,ub4 *legs,ub4 *predurs,ub4 nleg,ub4 costlim)
{
  struct chop *hp,*prvhp,*hops = net->chops;
  struct port *pdep,*ports = net->ports;
  struct route *rtp,*routes = net->routes;
  ub4 chopcnt = net->chopcnt;
  ub4 deptmin = src->deptmin;
  ub4 deptmax = src->deptmax;
  ub4 ttdurs[Nleg];

  ub8 x1,x2,prvx,*ev,*ev2,*events = net->cevents;

  struct srcres *rp,*res = src->res;

  ub4 evcnt,evcnt2,l,h,prvh;
  ub4 t1,t2,t22,dur,dur2,dt,prvt1,prvt2,t2e,t1b;
  ub4 tdep,tarr,cost;
  ub4 dtndx,dtcnt = 0;
  ub4 gt0 = net->t0;

  ub4 th,tf = deptmin - gt0;

  ub4 ei1 = 0,ei2 = 0;

  ub4 ttmin;

  ub4 td = 0,ta;
  ub4 eiarr,ei = 0;
  ub4 rescnt,ri = 0;

  ub8 x;

  if (nleg > Nleg) { errorfln(FLN,0,fln,"nleg %u above max %u",nleg,Nleg); return costlim; }
  else if (nleg == 0) { errorfln(FLN,0,fln,"nil nlegs"); return costlim; }
  else if (nleg == 1) { errorfln(FLN,0,fln,"nleg 1"); return costlim; }
  h = legs[0];
  if (h >= chopcnt) { errorfln(FLN,0,fln,"leg 0 hop %u >= %u",h,chopcnt); return costlim; }
  hp = hops + h;

  evcnt = hp->evcnt;
  if (evcnt == 0) return costlim;
  rtp = routes + hp->rid;

  ev = events + hp->evofs;

  rp = res;
  tdep = locate(FLN,rtp,ev,evcnt,tf,&ei,&x,&prvx);
  if (tdep < tf) return costlim;
  rp->td[0] = tdep;
  rp->hop[0] = h;
  dur = (x >> Durshift) & Durlim;
  ta = tdep + dur;

/*  ---\
        ...---\
        mtt    ...---
               mtt   \
 */

  for (l = 1; l < nleg; l++) {
    prvh = h;
    prvhp = hp;
    h = legs[l];
    hp = hops + h;
    rtp = routes + hp->rid;
    ttdurs[l] = predurs[l] + prvhp->hidur;
    ttmin = predurs[l];
    tf = ta + ttmin;

    ev = events + hp->evofs;
    evcnt = hp->evcnt;
    if (evcnt == 0) return costlim;
    td = locate(FLN,rtp,ev,evcnt,tf,&ei,&x,&prvx);
    if (td < tf) return costlim;
    rp->td[l] = td;
    rp->x[l] = x;
    rp->hop[l] = h;
    dur = (x >> Durshift) & Durlim;
    ta = td + dur;
  }
  tarr = ta;
  if (tarr < tdep) {
    warn(0,"tarr \ad%u below tdep \ad%u",tarr + gt0,tdep + gt0);
    return costlim;
  }
  l = nleg - 1;

#if 1
  // adjust backward for later initial departures
  while (l) {
    prvh = h;
    prvhp = hp;
    h = legs[l];
    hp = hops + h;
    rtp = routes + hp->rid;

    th = td - min(ttdurs[l],td); // latest allowed
    l--;
    if (th <= rp->td[l]) continue;

    ev = events + hp->evofs;
    evcnt = hp->evcnt;
    if (evcnt == 0) break;
    td = locate(FLN,rtp,ev,evcnt,th,&ei,&x,&prvx);
    if (td < th) break;
    else if (td <= rp->td[l]) continue;
    else if (td > th) {
      td = prvx & Timlim;
      rp->x[l] = prvx;
    } else rp->x[l] = x;
    if (td <= rp->td[l]) continue;
    rp->td[l] = td;
  }
  if (l == 1 && tdep > td) tdep = td;
#endif

  // for reserved transport legs, search for alternatives earlier

  if (tarr < tdep) {
    warn(0,"tarr \ad%u below tdep \ad%u",tarr + gt0,tdep + gt0);
    return costlim;
  }
  cost = tarr - tdep;

  // adjust for #transfers and walk dist
  if (cost >= costlim) return cost;

  rp->cost = cost;
  rp->nleg = (ub2)nleg;
  src->locost = cost;
  src->lores = 0;
  src->rescnt = ri;

  return cost;
}
#endif

// create list of candidate events for first leg
static ub4 mkdepevs(search *src,lnet *net,ub4 hop,ub4 costlim,int dbg)
{
  ub4 deptmin = src->deptmin;
  ub4 deptmax = src->deptmax;
  ub4 udeptmax = src->udeptmax;
  ub4 dcnt = 0,lodev,lodev2,gencnt;
  ub4 gndx,dmax = Maxevs;
  ub4 t,dur;
  ub2 *dev,*devp;
  ub2 srda;
  ub2 dtid;
  struct chop *chp,*chops = net->chops;
  struct port *pdep,*ports = net->ports;
  ub4 *portsbyhop = net->portsbyhop;
  ub4 chopcnt = net->chopcnt;
  ub8 cx,*cev,*cevents = net->cevents;
  ub4 cx2,*cev2,*cevents2 = net->cevents2;
  // ub1 *srarrp,*srarrs = net->evsrarrs;
  ub4 ofs;
  ub2 fare;
  ub2 *farepos,*fareposbase = net->fareposbase;
  ub4 cost = 0,locost;
  ub4 gt0 = net->t0;
  enum srcmodes mode = src->srcmode;

  src->dcnts[0] = src->dcnts[1] = 0;
  src->hops[0] = src->hops[1] = hi32;
  src->nleg = 0;

  if (hop >= chopcnt) return error(Ret0,"unexpected walk link %u on initial leg",hop);
  chp = chops + hop;

  pdep = ports + portsbyhop[hop * 2];

  gencnt = chp->evcnt;

  ub4 t0 = chp->t0;
  ub4 t1 = chp->t1;

  ub4 extracost;

  // srarrp = srarrs + chp->sdaofs;

  infocc(dbg,0,"leg 0 hop %u evs %u tt range \ad%u-\ad%u, dep window \ad%u-\ad%u %s",hop,gencnt,t0,t1,deptmin,deptmax,pdep->iname);

  if (gencnt == 0) return info(Notty,"no events for hop %u at \ad%u - \ad%u",hop,t0,t1);

  if (t0 == t1) return info(Iter|Notty,"hop %u tt range %u-%u, dep window %u-%u",hop,t0,t1,deptmin,deptmax);

  locost = hi32;

  cev = cevents + chp->evofs;
  cev2 = cevents2 + chp->evofs;

  dev = src->depevs[0];

  if (chkdev(dev,0)) return 0;

  // if out of departure window, take a single event
  if (t0 > deptmax) {
    gencnt = 1;
    info(Notty|Iter,"hop %u \ad%u - \ad%u after dep window \ad%u - \ad%u",hop,t0,t1,deptmin,deptmax);

  } else if (t1 <= deptmin) {
    info(Notty|Iter,"hop %u \ad%u - \ad%u before dep window \ad%u - \ad%u",hop,t0,t1,deptmin,deptmax);
    return 0;
  } else if (deptmin < gt0 || deptmax <= gt0) return info(Notty,"dep window \ad%u - \ad%u before net star \ad%u",deptmin,deptmax,gt0);

  deptmin -= gt0;
  deptmax -= gt0;

  ub4 lodur = chp->lodur;

  if (chp->reserve && net->fhopofs) {
    ofs = net->fhopofs[hop];
    farepos = fareposbase + ofs * Faregrp;
  } else farepos = NULL;
  fare = chp->fare;

  t = chp->t0 - gt0;
  lodev = lodev2 = hi32;

  for (gndx = 0; gndx < gencnt; gndx++) {
    cx = cev[gndx];
    t = cx & Timlim;

    if (t < deptmin) continue;
    else if (t >= deptmax) {
      if (gencnt > 1) break;
      if (udeptmax) extracost = t - deptmax;
      else extracost = 0;
    } else extracost = 0;

    // add minor bias to prefer times around given date/time
#if 0
    if (t < deptmid) {
      deptbias = deptmid - t;
      extracost += min(deptbias,1440) / 50;
      if (deptbias > 1440) extracost += (deptbias - 1440) / 200;
    } else if (t - deptmid > 180) {
      deptbias = t - deptmid;
      extracost += min(deptbias,1440) / 200;
      if (deptbias > 1440) extracost += (deptbias - 1440) / 400;
    }
#endif

    dur = (ub4)(cx >> Durshift) & Durlim;

    if (farepos) {
      fare = farepos[gndx * Faregrp];
      if (fare == hi16) continue;
    }

//    if (dur >= durlim) dur = midur;
//    error_eq(dur,hi32);

    switch (mode) {
    case Srclotime:
    case Srchitime: // cost is mainly duration. transfer cost is added at the end
      cost = Hitime(dur,fare);
      break;
    case Srcxtime: // cost is only duration. transfer cost is added at the end
      cost = dur;
      break;
    case Srclofare:
    case Srchifare:
      cost = Hifare(dur,fare);
      break;
    case Srcxfare:
      cost = fare;
      break;
    case Srcmodecnt: return error(0,"unknown search mode %u",mode);
    }

    cost += extracost;

    if (cost >= costlim) continue;

    cx2 = cev2[gndx];
    dtid = cx2 & hi16;
    srda = (ub2)(cx2 >> 16);

    if (chp->varsda) {
      // srda = (ub2)((srda & 0xff00) | srarrp[gndx]);
//      error_ge(srda & 0xff,pdep->subcnt);
    } else {
//      error_ge(srda & 0xff,pdep->subcnt);
    }

    devp = dev + dcnt * fldcnt;

    devp[timefld] = (ub2)t;
    devp[tidfld] = dtid;  // not needed, can search from t at getevs
    devp[durfld] = (ub2)dur;
    devp[sdurfld] = 0;
    devp[costfld] = (ub2)cost; // not needed here ?
    devp[farefld] = fare;
    devp[prvfld] = hi16;
    devp[sdafld] = srda;

    track(devp,1);

    if (cost < locost) {
      // infocc(dbg,Notty," hop %u t \ad%u cost %u",hop,t,cost);
      locost = cost;
      lodev = dcnt;
    } else if (cost == locost && lodev2 == hi32) lodev2 = dcnt;  // support 'next trip in <time>'
    dcnt++;
    if (dcnt >= dmax) {
      warning(Notty,"exceeding %u dep event",dcnt);
      break;
    }
  }
  src->dcnts[0] = dcnt;
  if (dcnt == 0) return 0;

  src->nleg = 1;

  src->hops[0] = hop;

  src->costcurs[0] = locost;
  src->devcurs[0] = lodev;
  src->devcurs2[0] = lodev2;
  warncc(lodev >= dcnt,Notty,"leg 0 lodev %u cnt %u",lodev,dcnt);
  infocc(vrbena,Notty,"%u dep events for leg 0",dcnt);
  if (chkdev(dev,0)) return 0;
  return dcnt;
}

// create list of candidate events for subsequent legs
static ub4 nxtevs(search *src,lnet *net,ub4 leg,ub4 hop,ub4 costlim,int dbg)
{
  ub4 aleg,ahop;
  ub4 dndx,dcnt,gencnt;
  ub4 gndx,agndx,prvgndx,dmax = Maxevs;
  ub4 adndx,adcnt,ofs;
  ub4 t,prvta,last,at,atarr,adur,asdur,lodt,dt,dur;
  ub2 srda,rt;
  ub2 dtid,fare,afare;
  ub4 lodev,lodev2;
  ub2 *dev,*adev,*devp,*adevp;
  ub4 cost = 0,locost,acost;
  struct chop *chp,*achp,*chops = net->chops;
  struct port *pdep,*ports = net->ports;
  ub4 chopcnt = net->chopcnt;

  ub4 *portsbyhop = net->portsbyhop;
  ub1 *smp,*smaps = net->submaps;

  ub8 cx,*cev,*cevents = net->cevents;
  ub4 cx2,*cev2,*cevents2 = net->cevents2;
  // ub1 *srarrp,*srarrs = net->evsrarrs;
  ub4 rid;
  ub2 *farepos,*fareposbase = net->fareposbase;
  ub4 sdur,srdur,asrda,asrarr,srdep;
  ub4 gt0 = net->t0;

  error_z(leg,0);
  aleg = leg - 1;

  src->dcnts[leg] = 0;
  if (leg + 1 < Nleg) src->dcnts[leg+1] = 0;
  if (src->nleg < leg) return error(Ret0,"nleg %u vs %u",src->nleg,leg);

  if (hop >= chopcnt) return warn(Iter,"walk link not expected for %u",hop);

  enum srcmodes mode = src->srcmode;

  chp = chops + hop;

  rid = chp->rid;

  pdep = ports + portsbyhop[hop * 2];
  smp = smaps + pdep->smapofs;

  gencnt = chp->evcnt;
  ub4 lodur = chp->lodur;
  infocc(dbg,Notty,"leg %u hop %u lodur \at%u evs %u",leg,hop,lodur,gencnt);

  if (gencnt == 0) return 0;

  // srarrp = srarrs + chp->sdaofs;

  ub4 t0 = chp->t0;

  adcnt = src->dcnts[aleg];
  if (adcnt == 0) return 0;

  // early out on best duration above best total
  locost = src->costcurs[aleg];
  if (mode == Srcxtime && locost + lodur > costlim) return 0;

  // infocc(dbg,0,"hop %u evs %u tt range \ad%u-\ad%u, dep window \ad%u-\ad%u",hop,gencnt,t0,t1,deptmin,deptmax);

  if (chp->reserve && net->fhopofs) {
    ofs = net->fhopofs[hop];
    farepos = fareposbase + ofs * Faregrp;
  } else farepos = NULL;
  fare = chp->fare; // default to static fare

  ub4 arid = hi32;
  ub8 evofs = chp->evofs;

  ub4 rngdur = chp->hidur - lodur;

  ahop = src->hops[aleg];
  if (ahop == hi32) { src->errcnt++; return warn(0,"no prv hop for %u leg %u",hop,aleg); }
  achp = chops + ahop;

  ub4 ttmin = getmintt(src->mintts,achp->kind,chp->kind);

  // first walk arrivals have no transfer time
  if (ahop >= chopcnt && leg == 1 && chp->kind != Airint && chp->kind != Airdom && chp->kind != Ferry) ttmin = 0;

  arid = achp->rid;
  if (arid != hi32 && rid == arid) ttmin = 0;  // same route has no transfer time

  cev = cevents + evofs;
  cev2 = cevents2 + evofs;
  cx = cev[0];

  dev = src->depevs[leg];
  adev = src->depevs[aleg];

  if (chkdev(dev,leg)) return 0;
  if (chkdev(dev,aleg)) return 0;

  locost = lodt = hi32; lodev = lodev2 = hi32;

  prvgndx = gndx = agndx = adndx = 0;
  t = t0 - gt0;
  dcnt = dndx = last = 0;

  if (chp->overtake == 0) {

    while (adndx < adcnt && dcnt < dmax) {
      adevp = adev + adndx * fldcnt;
      at = adevp[timefld];
      adur = adevp[durfld];
      asdur = adevp[sdurfld];

      atarr = at + adur + asdur;

      // infocc(dbg,Notty," andx %u/%u at \ad%u gndx %u/%u",adndx,adcnt,at + 600,prvgndx,gencnt);

      // search first candidate departure
      // if reference, push current offset, get time and duration offset and move back
      // pop if at end of referece
      while (gndx < gencnt) {
        cx = cev[gndx];
        t = (cx & Timlim);
        if (t >= atarr + ttmin) break;
        gndx++;
      }

      if (gndx == gencnt) break;

      acost = adevp[costfld];
      afare = adevp[farefld];

      // infocc(dbg,Notty|Noiter," hop %u first dep \ad%u after arr \ad%u ev %u/%u costlim %u",hop,t + gt0,atarr + gt0,gndx,gencnt,costlim);

      dur = (ub4)(cx >> Durshift);

      if (farepos) {
        fare = farepos[gndx * Faregrp];
        if (fare == hi16) {
          gndx++;
          continue;
        }
      }

      dt = t - atarr + dur;

      switch (mode) {
      case Srclotime:
      case Srchitime: // cost is mainly duration. transfer cost is added at the end
        cost = Hitime(dt,fare);
        break;
      case Srcxtime: // cost is only duration. transfer cost is added at the end
        cost = dt;
        break;
      case Srclofare:
      case Srchifare:
        cost = Hifare(dt,fare);
        break;
      case Srcxfare:
        cost = fare;
        break;
      case Srcmodecnt: return error(0,"unknown search mode %u",mode);
      }

      cost += acost;
      if (cost >= costlim) { adndx++; continue; }

      asrda = adevp[sdafld];
      asrarr = asrda & 0xff;

      cx2 = cev2[gndx];
      srda = (ub2)(cx2 >> 16);

      srdep = srda >> 8;
      if (chp->varsda) {
        // srda = (ub2)((srda & 0xff00) | srarrp[gndx]);
      }

      // adjust min txtime for member stops
      if (asrarr != srdep && asrarr != 0xff && srdep != 0xff) {
        srdur = srdep * pdep->subcnt + asrarr;
        sdur = smp[srdur];
        if (t < atarr + sdur + ttmin /* || cost + sdur >= costlim */) {
          adndx++;
          continue;
        }
        if (mode <= Srcxtime) cost += sdur;
      } else sdur = 0;

      rt = (ub2)t;

      // new entry
      // infocc(dbg,Notty|Noiter,"any \ad%u at idx %u",t + 660,dcnt);
      dndx = dcnt;
      if (dcnt + 1 >= dmax) break;
      devp = dev + dcnt++ * fldcnt;

      // infocc(dbg,Notty,"hop %u ahop %u t \ad%u cost %u",hop,ahop,t + 660,cost);

      dtid = cx2 & hi16;

      error_ge(dur,hi16);
      error_ge(cost,hi16);

      devp[timefld] = rt;
      devp[tidfld] = dtid;
      devp[durfld] = (ub2)dur;
      devp[sdurfld] = (ub2)sdur;
      devp[costfld] = (ub2)cost;
      devp[prvfld] = (ub2)adndx;
      devp[farefld] = (ub2)(fare + afare);
      track(devp,2);
      devp[sdafld] = srda;

      if (cost < locost) {
        locost = cost;
        lodev = dndx;
      } else if (cost == locost && lodev2 == hi32) lodev2 = dndx;

      adndx++;

  } // each prvarr

 } else {

  // idem, supporting later deps to overtake preceding
  // todo: not for zevents ?
  while (adndx < adcnt && dcnt < dmax) {
    adevp = adev + adndx * fldcnt;
    at = adevp[timefld];
    adur = adevp[durfld];
    asdur = adevp[sdurfld];

    atarr = at + adur + asdur;

    // search first candidate departure
    // note that the output event may already have been written for last iter
    gndx = prvgndx;

    // infocc(dbg,Notty," andx %u/%u at \ad%u gndx %u/%u",adndx,adcnt,at + 600,prvgndx,gencnt);

    while (gndx < gencnt) {
      cx = cev[gndx];
      t = (cx & Timlim);
      if (t >= atarr + ttmin) break;
      gndx++;
    }

    if (gndx == gencnt) break;

    acost = adevp[costfld];
    asrda = adevp[sdafld];
    asrarr = asrda & 0xff;
    afare = adevp[farefld];

    // infocc(dbg,Notty|Noiter," hop %u first dep \ad%u after arr \ad%u ev %u/%u costlim %u",hop,t + gt0,atarr + gt0,gndx,gencnt,costlim);
    prvgndx = gndx;
    prvta = hi32;

    while (gndx < gencnt) {
      cx = cev[gndx];
      t = (cx & Timlim);

      // cannot be better than previous
      if (mode == Srcxtime && t + lodur >= prvta) break;
      prvta = t + lodur;

      dur = (ub4)(cx >> Durshift);

      dt = t - atarr + dur;

      // infocc(dbg,Notty|Noiter,"  dep \ad%u dur %u cost %u lim %u ev %u",t + gt0,dur,cost,costlim,gndx);

      if (farepos) {
        fare = farepos[gndx * Faregrp];
        if (fare == hi16) {
          gndx++;
          continue;
        }
      }

      switch (mode) {
      case Srclotime:
      case Srchitime: // cost is mainly duration. transfer cost is added at the end
        cost = Hitime(dt,fare);
        break;
      case Srcxtime: // cost is only duration. transfer cost is added at the end
        cost = dt;
        break;
      case Srclofare:
      case Srchifare:
        cost = Hifare(dt,fare);
        break;
      case Srcxfare:
        cost = fare;
        break;
      case Srcmodecnt: return error(0,"unknown search mode %u",mode);
      }

      cost += acost;
      if (cost >= costlim) {
        gndx++;
        if (rngdur == 0) break;
        else { gndx++; continue; }
      }

      cx2 = cev2[gndx];
      srda = (ub2)(cx2 >> 16);

      srdep = srda >> 8;

#if 0
      if (srarrp) {
        srda = (ub2)((srda & 0xff00) | srarrp[gndx]);
      }
#endif
      gndx++;

      // adjust min txtime for member stops
      if (asrarr != srdep && asrarr != 0xff && srdep != 0xff && srdep < pdep->subcnt && asrarr < pdep->subcnt) {
        srdur = srdep * pdep->subcnt + asrarr;
        sdur = smp[srdur];
        if (t < atarr + sdur + ttmin || cost + sdur >= costlim) {
          continue;
        }
        if (mode <= Srcxtime) cost += sdur;
      } else sdur = 0;

      rt = (ub2)t;

      if (t > last || dcnt == 0) {  // new entry
        // infocc(dbg,Notty|Noiter,"any \ad%u at idx %u",t + 660,dcnt);
        dndx = dcnt;
        if (/* dcnt >= ddcnt || */ dcnt + 1 >= dmax) break;
        devp = dev + dcnt++ * fldcnt;

        last = t;

      } else { // written in earlier pass or unordered
        dndx = dcnt;

        do {   // search matching entry
          dndx--;
          devp = dev + dndx * fldcnt;
          if (devp[timefld] == rt) break;
        } while (dndx);
        if (devp[timefld] == rt) {
          // infocc(dbg,Notty|Noiter,"found \ad%u at idx %u",t + 660,dndx);
          if (cost >= devp[costfld]) {
            continue; // overwrite only if better
          }
        } else {
          // infocc(dbg,Notty|Noiter,"new \ad%u at idx %u",t + 660,dcnt);
          dndx = dcnt;
          if (dcnt + 1 >= dmax) break;
          devp = dev + dcnt++ * fldcnt;
          last = t;
        }
      }

      // infocc(dbg,Notty,"hop %u ahop %u t \ad%u cost %u",hop,ahop,t + 660,cost);

      dtid = cx2 & hi16;

      error_ge(dur,hi16);
      error_ge(cost,hi16);

      devp[timefld] = rt;
      devp[tidfld] = dtid;
      devp[durfld] = (ub2)dur;
      devp[sdurfld] = (ub2)sdur;
      devp[costfld] = (ub2)cost;
      devp[prvfld] = (ub2)adndx;
      devp[farefld] = (ub2)(fare + afare);
      track(devp,3);
      devp[sdafld] = srda;

      if (cost < locost) {
        locost = cost;
        lodev = dndx;
      } else if (cost == locost && lodev2 == hi32) lodev2 = dndx;

    } // each dep

    adndx++;
  } // each prvarr

 } // overtake or not

  if (chkdev(dev,leg)) return 0;
  if (chkdev(dev,aleg)) return 0;
  src->dcnts[leg] = dcnt;
  if (dcnt == 0) return 0;

  warncc(dcnt >= dmax,0,"exceeding %u dep event",dcnt);
  if (lodev >= dcnt) return warn(0,"leg %u lodev %u cnt %u",leg,lodev,dcnt);

  src->nleg = leg + 1;

  src->hops[leg] = hop;

  src->costcurs[leg] = locost;
  src->devcurs[leg] = lodev;
  src->devcurs2[leg] = lodev2;
  src->devttmin[leg] = ttmin;
  infocc(vrbena,Notty,"%u dep events for leg %u, locost %u",dcnt,leg,locost);
  return dcnt;
}

// forward existing evs, e.g. walk link after nonwalk
static ub4 fwdevs(search *src,lnet *net,ub4 leg,ub4 ahop,ub4 hop,ub4 midur,ub4 costlim)
{
  ub4 aleg;
  ub4 dcnt = 0;
  ub4 dmax = Maxevs;
  ub4 adndx,adcnt;
  ub4 t,at,dt,adur,asdur,acost,lodev,lodev2,lodt;
  ub2 rt;
  ub2 *dev,*adev,*devp,*adevp;
  ub2 afare,fare = 0;
  ub2 asrda,asrarr;
  ub4 locost,cost;
  ub4 ttmin;
  struct chop *achp,*chp,*chops = net->chops;
  enum srcmodes mode = src->srcmode;

  error_z(leg,hop);
  error_ge(midur,hi16);

  src->dcnts[leg] = 0;
  if (leg + 1 < Nleg) src->dcnts[leg+1] = 0;

  aleg = leg - 1;
  if (src->nleg < leg) return error(Ret0,"nleg %u vs %u",src->nleg,leg);

  adcnt = src->dcnts[aleg];
  if (adcnt == 0) return 0;

  cost = src->costcurs[aleg];

  if (cost >= costlim) return 0;

  dev = src->depevs[leg];
  adev = src->depevs[aleg];

  if (chkdev(dev,leg)) return 0;
  if (chkdev(dev,aleg)) return 0;

  achp = chops + ahop;
  chp = chops + hop;

  ttmin = getmintt(src->mintts,achp->kind,chp->kind);

  locost = lodt = hi32; lodev = lodev2 = hi32;
  adndx = 0;
  while (adndx < adcnt && dcnt < dmax) {
    adevp = adev + adndx * fldcnt;
    at = adevp[timefld];
    adur = adevp[durfld];
    asdur = adevp[sdurfld];
    acost = adevp[costfld];
    afare = adevp[farefld];
    asrda = adevp[sdafld];
    asrarr = asrda & 0xff;

    t = at + adur + asdur + ttmin;

    dt = midur + ttmin;

    switch (mode) {
    case Srclotime:
    case Srchitime: // cost is mainly duration. transfer cost is added at the end
      cost = Hitime(dt,fare);
      break;
    case Srcxtime: // cost is only duration. transfer cost is added at the end
      cost = dt;
      break;
    case Srclofare:
    case Srchifare:
      cost = Hifare(dt,fare);
      break;
    case Srcxfare:
      cost = fare;
      break;
    case Srcmodecnt: return error(Ret0,"unknown search mode %u",mode);
    }

    cost += acost;

    if (cost >= costlim) { adndx++; continue; }

    rt = (ub2)t;
    devp = dev + dcnt * fldcnt;
    devp[timefld] = rt;
    devp[tidfld] = hi16;
    devp[durfld] = (ub2)midur;
    devp[sdurfld] = 0;
    devp[prvfld] = (ub2)adndx;
    devp[farefld] = (ub2)(afare + fare);
    devp[sdafld] = (ub2)(asrarr << 8) | 0xff;
    track(devp,4);

    devp[costfld] = (ub2)cost;

    if (cost < locost) { locost = cost; lodev = dcnt; }
    else if (cost == locost && lodev2 == hi32) lodev2 = dcnt;
    dcnt++;

    adndx++;
  }
  if (chkdev(dev,leg)) return 0;
  if (chkdev(dev,aleg)) return 0;
  src->dcnts[leg] = dcnt;
  if (dcnt == 0) return 0;
  if (lodev >= dcnt) return warn(0,"leg %u lodev %u cnt %u",leg,lodev,dcnt);

  src->nleg = leg + 1;

  src->hops[leg] = hop;

  src->costcurs[leg] = locost;
  // src->dtlos[leg] = lodt;
  src->devcurs[leg] = lodev;
  src->devcurs2[leg] = lodev2;
  src->devttmin[leg] = ttmin;
  infocc(vrbena,Notty,"%u dep events for leg %u",dcnt,leg);

  return dcnt;
}

// extract trip after best found
#define getevs(src,net,nleg,legs,topn,desc) getevsfln(FLN,(src),(net),(nleg),(legs),(topn),(desc))

static ub4 getevsfln(ub4 fln,search *src,lnet *net,ub4 nleg,ub4 *legs,ub4 topn,const char *desc)
{
  ub4 hopcnt = net->hopcnt;
  ub4 chopcnt = net->chopcnt;
  ub4 whopcnt = net->whopcnt;
  ub4 tidcnt = net->chaincnt;
  ub4 dcnt = 0;
  ub4 lodev,nxtlodev,l;
  ub4 t,tid,dtid,at,dur,sdur,dt,cost,srdep,srarr,nxsrdep,srda,ttmin;
  ub2 *dev,*devp;
  ub4 *lodevs = src->devcurs;
  ub4 *lodevs2 = src->devcurs2;
  ub4 rid;
  ub4 hop,hop1,hop2,nxthop;
  ub4 fare;
  ub4 *routechains = net->routechains;
  struct port *parr,*ports = net->ports;
  struct chop *hp,*hops = net->chops;
  ub4 *portsbyhop = net->portsbyhop;
  struct route *rp;
  ub4 gt0 = net->t0;
  ub4 errcnt = src->errcnt;

#if Track
  ub4 tfln
#endif

  return 1;

  error_z(nleg,0);

  src->de_prvhop = hi32;

  if (nleg != src->nleg) return errorfln(FLN,Ret0,fln,"nleg %u vs %u %s",nleg,src->nleg,desc);

  dt = hi32;
  at = hi32;
  nxthop = hi32;
  nxsrdep = 0xff;
  l = nleg - 1;
  if (topn == 0) {
    lodev = lodevs[l];
    if (lodev == hi32) return warnfln2(FLN,0,fln,"no events for leg %u",l);
  } else {
    lodev = lodevs2[l];
    if (lodev == hi32) return 0;
  }
  dcnt = src->dcnts[l];
  if (dcnt == 0) return warnfln2(FLN,0,fln,"no events for leg %u",l);
  else if (lodev >= dcnt) return warnfln2(FLN,0,fln,"lodev %u cnt %u for leg %u",lodev,dcnt,l);

  do {
    dev = src->depevs[l];
    dcnt = src->dcnts[l];
    ttmin = src->devttmin[l];

    if (dcnt == 0) return warnfln2(FLN,0,fln,"no events for leg %u",l);

    if (chkdev(dev,l)) return 0;

    hop = src->hops[l];
    if (hop != legs[l]) return errorfln(FLN,Ret0,fln,"leg %u hop %u vs %u at pos %u",l,hop,legs[l],lodev);
    if (hop >= whopcnt) return errorfln(FLN,Ret0,fln,"leg %u invalid hop %u at pos %u",l,hop,lodev);

    if (hop < hopcnt || hop >= chopcnt) { hop1 = hop; hop2 = hi32; }
    else {
      hp = hops + hop;
      hop1 = hp->hop1; hop2 = hp->hop2;
    }

    if (hop2 >= hopcnt && hop2 < chopcnt) {
      warnfln2(FLN,0,fln,"hop %u from %u = %u is compound",hop2,hop,hop1);
      errcnt++;
    }

    devp = dev + lodev * fldcnt;
    t = gt0 + devp[timefld];
    dtid = devp[tidfld];
    cost = devp[costfld];
    dur = devp[durfld];
    sdur = devp[sdurfld];
    srda = devp[sdafld];

#if Track
    tfln = devp[flnfld];
#endif

//    infofln2(tfln,Notty,FLN,"t \ad%u + %u = \ad%u",gt0,devp[timefld],t);

    hp = hops + hop1;
    tid = hi32;
    if (hop1 < hopcnt) {
      if (dtid != hi16) {
        rid = hp->rid;
        vrb0(0,"dtid %u rid %u of %u",dtid,rid,net->ridcnt);
        if (rid < net->ridcnt) {
          rp = net->routes + rid;
          if (rp->chainofs + dtid < net->chaincnt) tid = routechains[rp->chainofs + dtid];
          else {
            errcnt++;
            warnfln2(FLN,0,fln,"hop %u rid %u dtid %u not in %u",hop1,rid,dtid,rp->chaincnt);
          }
          vrb0(0,"tid %u",tid);
        } else {
          errcnt++;
          warnfln2(FLN,0,fln,"hop %u no rid %u",hop1,rid);
        }
      } else if (hp->kind != Taxi) {
        errcnt++;
        warnfln2(FLN,0,fln,"hop %u no dtid from %u",hop1,fln);
      }
    } else if (hop1 < chopcnt) {
      errcnt++;
      warnfln2(FLN,0,fln,"unexpected compound hop %u",hop1);
    }

    if (hop2 == hi32) parr = ports + portsbyhop[hop1 * 2 + 1];
    else parr = ports + portsbyhop[hop2 * 2 + 1];

    srdep = srda >> 8;
    srarr = srda & 0xff;
    if (srarr != 0xff) {
      if(srarr >= parr->subcnt) {
        warnfln2(FLN,Notty,fln,"leg %u dev %u sub %u not in %u-group port %u %s",l,lodev,srarr,parr->subcnt,parr->id,parr->iname);
        srarr = 0xff;
      }
    }

    // make walk links end at subsequent start subport
    if (hop1 >= chopcnt && nxthop != hi32) {
      srarr = nxsrdep;
    }
    nxthop = hop1;
    nxsrdep = srdep;

    if (srdep == 0xff) srdep = hi32;
    if (srarr == 0xff) srarr = hi32;

    if (lodev >= dcnt) return errorfln(FLN,Ret0,fln,"lodev %u cnt %u for leg %u hop %u at \ad%u",lodev,dcnt,l,hop1,t);

    nxtlodev = devp[prvfld];
    fare = devp[farefld];

    // info(0,"leg %u fare %u",l,fare);

    src->curcosts[l] = cost;

    // src->curdts[l] = dt;
    src->curdurs[l] = dur;
    src->cursdurs[l] = sdur;
    src->curts[l] = t;
    if (t == 0) return errorfln(FLN,Ret0,fln,"t 0 for lodev %u,%u leg %u",lodev,nxtlodev,l);

    src->curtids[l] = tid;
    src->curfares[l] = fare;
    src->cursdeps[l] = srdep;
    src->cursarrs[l] = srarr;

    // if (l == nleg - 1) src->curdt = dt;

    if (t && at < t) warnfln2(FLN,Iter,fln,"prvtdep \ad%u after tdep \ad%u",t,at);
    at = t;

    if (tid == hi32) {
      if(hop1 < chopcnt && hp->kind != Taxi) infofln2(FLN,Notty,fln,"%shop %u ev %u of %u leg %u t \ad%u dt %u no tid",
        hop < hopcnt ? "" : "c",hop1,lodev,dcnt,l,t,dt);
      else info(Notty|V0,"hop %u ev %u of %u leg %u t \ad%u dt %u",hop1,lodev,dcnt,l,t,dt);
    } else {
      if (hop1 >= chopcnt) return errorfln(FLN,Ret0,fln,"walk link %u with tid %u leg %u pos %u at \aD%u p %p",hop1,tid,l,lodev,t,(void *)devp);
      if (tid >= tidcnt) errorfln(FLN,0,fln,"leg %u tid %x tidcnt %u",l,tid,tidcnt);
      info(Notty|V0,"hop %u-%u ev %u of %u leg %u t \ad%u dur %u+%u tid %u dt %u mintt %u",hop1,hop2,lodev,dcnt,l,t,dur,sdur,tid,dt,ttmin);
    }
    lodev = nxtlodev;
  } while (lodev != hi32 && l && l--);
  if (l) return warnfln2(FLN,0,fln,"no lodev below leg %u",l);

  src->errcnt += errcnt;
  info(CC0,"%u errors %s",errcnt,desc);

  ub4 depwin = src->dephwin;
  src->curt = src->curts[0];
  src->curhwin = depwin;

  hop = src->dwhop;
  hp = hops + hop;
  info(0,"win %u hours %u at hop %u evs %u aid %u",depwin,src->dwday,hop,hp->evcnt,hp->aid);
  fmtstring(src->dwinfo,"%u.%u.%u",depwin,src->dwleg,hp->evcnt);
  return dcnt;
}

static int sametrip(struct trip *tp1,struct trip *tp2)
{
  ub4 len = tp1->len;

  if (len == 0 || len != tp2->len) return 0;
  if (memcmp(tp1->trip,tp2->trip,len * sizeof(ub4))) return 0;
  if (tp1->t[0] && tp2->t[0] && memcmp(tp1->t,tp2->t,len * sizeof(tp1->t[0]))) return 0;
  return 1;
}

#if 0
static struct trip *setrip(search *src,lnet *net,ub4 curcost,ub4 *pcostlim,ub4 nleg,ub4 *tp,const char *desc)
{
  struct trip *stp,*stp2,*trips = src->trips;
  ub4 ntop = src->ntop;
  ub4 tripno,leg,curt,sumdt,fare,h,tid;
  ub4 chopcnt = net->chopcnt;
  ub4 whopcnt = net->whopcnt;
  struct chop *hp,*hops = net->chops;

  return src->trips;

  if (nleg == 0) return nilerr(0,"%s: nleg 0",desc);
  else if (nleg >= Nleg) return nilerr(0,"%s: nleg %u above %u",desc,nleg,Nleg);

  // search slot with highest cost to fill
  ub4 locost = hi32, hicost = 0, hitrip = 0, lotrip = 0;
  for (tripno = 0; tripno < ntop; tripno++) {
    stp = trips + tripno;
    if (stp->len == 0) { hicost = curcost; hitrip = tripno; break; }
    if (stp->cost > hicost) { hicost = stp->cost; hitrip = tripno; }
  }
  if (hicost == 0) { hicost = curcost; hitrip = 0; }
  info(0,"set slot %u on hicost %u",tripno,hicost);

  // skip if not better
  stp = trips + hitrip;
  if (stp->len && curcost > stp->cost) return NULL;

  // skip if identical to any other
  for (tripno = 0; tripno < ntop; tripno++) {
    stp2 = trips + tripno;
    if (tripno == hitrip || stp2->len == 0) continue;
    if (stp->len != stp2->len) continue;
    if (sametrip(stp,stp2)) return NULL;
  }

  for (leg = 0; leg < nleg; leg++) {
    h = tp[leg];
    if (h >= whopcnt) return nilerr(0,"%s: hop %u above %u at leg %u",desc,h,whopcnt,leg);
    hp = hops + h;
    stp->trip[leg] = h;

    curt = src->curts[leg];
    if (curt == 0) return nilerr(0,"%s: t 0 at leg %u",desc,leg);
    stp->t[leg] = curt;
    stp->dur[leg] = src->curdurs[leg];
    stp->sdur[leg] = src->cursdurs[leg];
    tid = src->curtids[leg];
    stp->tid[leg] = tid;
    stp->srdep[leg] = src->cursdeps[leg];
    stp->srarr[leg] = src->cursarrs[leg];
    stp->fares[leg] = src->curfares[leg];

    if (tid == hi32 && h < chopcnt && hp->kind != Taxi) error(0,"%s: leg %u hop %u no tid",desc,leg,h);
    info(V0,"  leg %u %u,%u dep \ad%u dt %u evs %u",leg,src->cursdeps[leg],src->cursarrs[leg],curt,src->curdts[leg],src->dcnts[leg]);
  }

  stp->cost = curcost;
  stp->len = nleg;

  hicost = 0;
  for (tripno = 0; tripno < ntop; tripno++) {
    stp2 = trips + tripno;
    if (stp2->len == 0) continue;
    if (stp2->cost > hicost) hicost = stp2->cost;
    if (stp2->cost < locost) { locost = stp2->cost; lotrip = tripno; }
  }
  src->locost = locost;
  info(0,"add trip to slot %u cost %u lo %u at %u hi %u",hitrip,curcost,locost,lotrip,hicost);

  *pcostlim = hicost;

  src->ntrip = max(src->ntrip,hitrip + 1);

  leg = nleg - 1;
  sumdt = src->curts[leg] - src->curts[0] + src->curdurs[leg];
  fare = src->curfares[leg];
  stp->dt = sumdt;
  stp->fare = fare;
  return stp;
}
#endif

// store extra src result info
static void srcinfo(search *src,ub4 ndyn,ub4 nleg0,ub4 nleg1,ub4 nleg2,ub4 nleg3,ub4 i0,ub4 i1,ub8 dt)
{
  struct srcxres *xp = src->curxres + src->altpos;

  xp->ndyn = (ub2)ndyn;
  xp->nleg0 = nleg0;
  xp->nleg1 = nleg1;
  xp->nleg2 = nleg2;
  xp->nleg3 = nleg3;
  xp->i0 = i0;
  xp->i1 = i1;
  xp->dt = (ub4)dt;
}

static inline ub4 walkdur(ub4 dist,ub4 speed)
{
  return min(1 + (dist * 60) / speed,Durlim);
}

// accumulate connecting candidate events for each leg
#define addevs(src,net,legs,nleg,lim) addevsfln(FLN,src,net,(legs),nleg,(lim))
static ub4 addevsfln(ub4 fln,search *src,lnet *net, ub4 *legs,ub4 nleg,ub4 costlim)
{
  struct chop *hp,*prvhp,*hops = net->chops;
  ub4 whopcnt = net->whopcnt;
  ub4 thopcnt = net->thopcnt;
  ub4 chopcnt = net->chopcnt;
  ub4 hopcnt = net->hopcnt;
  ub4 gt0 = net->t0;
  ub4 midur;
  ub1 *modes = net->hopmodes;
  ub4 mintt,*mintts = src->mintts;
  ub4 wdist,tdist,*hopdist = net->hopdist;
  ub4 costperstop = src->costperstop;
  ub4 walkspeed = src->walkspeed;
  ub4 leg,bstop = 0,wstop = 0,cnt = 0;
  ub4 hop,nxthop,nxthop2,ahop;
  ub4 curcost,cost,whr,ttbias,deptmax;
  ub4 altpos;
  ub4 dur,lodur,sumdur,ttdur;
  ub4 td,prvtd,prvta;
  ub8 x;
  ub4 loevcnt = hi32;
  ub4 totlodur,lotx,totlotx;
  ub4 tcostlim;
  iadrbase *hoptx = &net->hoptx;
  ub4 *statp = src->addstat;
  enum srcmodes mode = src->srcmode;
  struct srcres *drp,*srp;
  ub4 evlegs[Nleg];   // [nevleg]
  ub4 predurs[Nleg];  // [nevleg]
  ub4 noevdurs[Nleg]; // [nleg]
  ub4 nevleg,evleg;
  ub4 hfpos;
  char hinfos[256];
  ub4 hinfolen = sizeof(hinfos);
  int tmode = (mode <= Srcxtime);

  hinfos[0] = 0;

  if (costlim == 0) { warnfln2(fln,0,FLN,"nil cost for %u leg\as",nleg); return hi32; }
  if (nleg == 0) { errorfln(fln,0,FLN,"empty trip"); return costlim; }
  else if (nleg >= Nleg) { errorfln(fln,0,FLN,"overlong trip len %u",nleg); return costlim; }
  else if (nleg == 1) {
    hop = legs[0];
    hp = hops + hop;
    lodur = hp->lodur;
    src->combicnt++;
    switch(hp->kind) {
    case Walk:
      lodur = walkdur(hp->dist,walkspeed);
    case Taxi:
      cost = lodur;
      if (cost >= costlim) return cost;

      // mimick srcevs output
      lodur = min(lodur,Durlim);
      src->lores = 0;
      srp = src->res;
      srp->hop[0] = hop;
      srp->td[0] = src->deptmin - gt0;
      srp->x[0] = (ub8)lodur << Durshift;
      srp->nleg = 1;
      break;
    case Airint: case Airdom: case Rail: case Bus: case Ferry:
      if (lodur >= costlim) return costlim;
      cost = srcevs1(fln,src,net,hop,costlim);
      break;
    case Unknown: case Kindcnt:
      hopmsgfln(fln,Error,0,hop,"src.%u invalid hop",__LINE__);
      return costlim;
    }
    if (cost >= costlim) return cost;

    hfpos = fmtstring(hinfos,"%c%c%u",hp->ctype,hp->ckind,hop);

    evleg = 0;
    nevleg = 1;
  } else {

    src->combicnt++;
    nevleg = 0;
    cost = 0;
    mintt = 0;
    sumdur = 0;
    memset(predurs,0,nleg * sizeof(int));

    // handle non-event hops set up trip
    todo use estdur-based lotx2 as early-out
    hop = legs[0];
    hp = hops + hop;
    for (leg = 0; leg < nleg; leg++) {
      hop = legs[leg];
      prvhp = hp;
      hp = hops + hop;
      dur = hp->lodur;
      if (leg) mintt = getmintt(mintts,prvhp->kind,hp->kind);

      switch(hp->kind) {
      case Walk:
        dur = walkdur(hp->dist,walkspeed);
      case Taxi:
        noevdurs[leg] = dur + mintt;  // used to reconstruct after src
        sumdur += dur + mintt;
        predurs[nevleg] += dur + mintt;  //  incorporate as 'min xfer time' for event search
        break;

      case Airint: case Airdom: case Rail: case Bus: case Ferry:
        sumdur += dur + mintt;
        predurs[nevleg] += mintt; evlegs[nevleg] = hop;
        nevleg++;
        break;
      case Unknown: case Kindcnt:
        hopmsg(Error,0,hop,"leg %u/%u invalid hop",leg,nleg);
        return 1;
      }
    }

    if (sumdur >= costlim) return costlim;

    if (nevleg == 0) { // e.g. walk after walk
      cost = sumdur;
      if (cost >= costlim) return cost;

      altpos = src->altpos + 1;
      if (altpos >= Ntop) altpos = 0;
      src->altpos = altpos;
      drp = src->curres + altpos;
      src->lores = 0;

      td = src->deptmin - gt0;
      hfpos = 0;
      for (leg = 0; leg < nleg; leg++) {
        hop = legs[leg];
        hp = hops + hop;
        switch(hp->kind) {
          case Walk: dur = walkdur(hp->dist,walkspeed); break;
          case Taxi: dur = hp->lodur; break;
          case Airint: case Airdom: case Rail: case Bus: case Ferry:
          case Unknown: case Kindcnt: hopmsg(Error,0,hop,"leg %u/%u unexpected event hop",leg,nleg); return costlim;
        }

        ttdur = noevdurs[leg];

        // mimick srcevs output
        drp->hop[leg] = hop;
        drp->td[leg] = td;
        drp->x[leg] = (ub8)dur << Durshift;
        td += ttdur;

        hfpos += mysnprintf(hinfos,hfpos,hinfolen,"%c%c%u-",hp->ctype,hp->ckind,hop);
      }
      drp->nleg = (ub2)nleg;
      if (hfpos) hinfos[hfpos-1] = 0;
      info(0,"%u leg\as %u evleg\as cost %u from %u %s",nleg,nevleg,cost,costlim,hinfos);
      src->costlim = cost;
      return cost;

    } else if (nevleg == 1) cost = srcevs1(fln,src,net,evlegs[0],costlim);
    else cost = srcevs(fln,src,net,evlegs,predurs,nevleg,costlim);

    if (cost >= costlim) return cost;
    else if (cost == 0) { warnfln2(fln,0,FLN,"nil cost from %u for %u leg\as",costlim,nleg); return costlim; }
  } // nleg > 1

  // store current best besides previous
  altpos = src->altpos + 1;
  if (altpos >= Ntop) altpos = 0;
  src->altpos = altpos;
  drp = src->curres + altpos;
  srp = src->res + src->lores;

  evleg = 0;
  td = prvta = srp->td[0];
  hfpos = 0;
  for (leg = 0; leg < nleg; leg++) {
    hop = legs[leg];
    hp = hops + hop;
    prvtd = td;
    if (evleg < nevleg) td = srp->td[evleg];
    else {
      td = prvta;
    }
    if (td == 0) {
      info0(Nolvl,hinfos);
      hopmsg(Warn,0,hop,"leg %u/%u evleg %u/%u t zero",leg,nleg,evleg,nevleg); return costlim;
    } else if (td < prvtd) {
      info0(Nolvl,hinfos);
      hopmsg(Warn,0,hop,"L %u/%u,%u/%u t %u<%u \ad%u<\ad%u",leg,nleg,evleg,nevleg,td,prvtd,td + gt0,prvtd + gt0);
      return costlim;
    } else if (leg && td == prvtd) {
      info0(Nolvl,hinfos);
      hopmsg(Warn,0,hop,"L %u/%u,%u/%u t %u=%u \ad%u=\ad%u",leg,nleg,evleg,nevleg,td,prvtd,td + gt0,prvtd + gt0);
      return costlim;
    }
    x = srp->x[evleg];
    switch(hp->kind) {
    case Walk:
      dur = walkdur(hp->dist,walkspeed);
      if (td < dur) { warnfln2(fln,0,FLN,"leg %u td %u < dur %u",leg,td,dur); return costlim; }
      if (evleg < nevleg) td -= dur;
      x = dur << Durshift;
      break;
    case Taxi:
      dur = hp->lodur;
      if (td < dur) { warnfln2(fln,0,FLN,"leg %u td %u < dur %u",leg,td,dur); return costlim; }
      if (evleg < nevleg) td -= dur;
      x = dur << Durshift;
      break;
    case Airint: case Airdom: case Rail: case Bus: case Ferry:
      x = srp->x[evleg];
      dur = (x >> Durshift) & Durlim;
      prvta = td + dur;
      evleg++;
      break;
    case Unknown: case Kindcnt: return 1;
    }
    drp->hop[leg] = hop;
    drp->td[leg] = td;
    drp->x[leg] = x;
    hfpos += mysnprintf(hinfos,hfpos,hinfolen,"%c%c%u-",hp->ctype,hp->ckind,hop);
  }
  drp->nleg = (ub2)nleg;
  if (hfpos) hinfos[hfpos-1] = 0;

  info(0,"legs %u.%u cost %u -> %u %s",nleg,evleg,costlim,cost,hinfos);
  src->costlim = cost;
  return cost;

#if 0
  hop = legs[nleg-1];
  hp = hops + hop;
  tcostlim = min(costlim,hp->hidur + net->tt1 - src->deptmin);
  if (tcostlim == 0) { warnfln(fln,0,"nil cost from %u for %u leg\as",costlim,nleg); return costlim; }

  // early out on lowest duration alone, or no events
  hop = legs[0];
  error_ge(hop,whopcnt);
  hp = hops + hop;
  lodur = totlodur = hp->lodur;
  if (lodur >= hi16 || (tmode && lodur >= tcostlim)) { statp[0]++; return costlim; }
  if (hop < chopcnt) loevcnt = min(loevcnt,hp->evcnt);

  for (leg = 1; leg < nleg; leg++) {
    hop = legs[leg];
    error_ge(hop,whopcnt);
    hp = hops + hop;
    lodur = hp->lodur;
    if (lodur >= hi16 || (tmode && lodur >= tcostlim)) { statp[1]++; return costlim; }
    totlodur += lodur;
    if (tmode && totlodur >= tcostlim) { statp[2]++; return costlim; }
    if (hop < chopcnt) loevcnt = min(loevcnt,hp->evcnt);
  }
  if (loevcnt == 0) { statp[3]++; return costlim; }

  // early out on lowest duration plus lowest txtime
  if (tmode && globs.nolotx == 0) {
    totlotx = 0;
    hop = legs[0];
    if (hop < chopcnt && hop >= hopcnt) hop = hops[hop].hop2;

    for (leg = 1; leg < nleg; leg++) {
      nxthop = legs[leg];
      if (nxthop < chopcnt && nxthop >= hopcnt) {
        nxthop = hops[nxthop].hop1;
        nxthop2 = hops[nxthop].hop2;
      } else nxthop2 = nxthop;
      if (hop < hopcnt && nxthop < hopcnt && modes[hop] != Taxibit && modes[nxthop] != Taxibit) {
        lotx = rdiadr2(hoptx,hop,nxthop);
        if (lotx == hi16 || lotx >= tcostlim) { statp[4]++; return costlim; }
        totlotx += lotx;
        if (totlotx + totlodur >= tcostlim) { statp[5]++; return costlim; }
      }
      hop = nxthop2;
    }
  }

  statp[6]++;
#endif

#if 0

   // autodetect departure time window
  if (src->udeptmax == 0) {
    if (nleg == 1 && *legs >= chopcnt) whr = 4;

    // else whr = getdepwin(src,net,legs,nleg);
    else whr = 12;

    // info(Notty,"depwin %u",whr);
    if (whr == 0) whr = 24;
    deptmax = min(src->deptmin + whr * 60,net->tt1);
    if (deptmax <= src->deptmin) { return 0; }
    src->dephwin = whr;
  } else deptmax = src->udeptmax;
  src->deptmax = deptmax;

  hop = legs[0];
  if (nleg > 1) {
    nxthop = legs[1];
    if (nxthop >= chopcnt || modes[nxthop] == Taxibit) nxthop = hi32;
  } else nxthop = hi32;
  error_ge(hop,whopcnt);
  hp = hops + hop;
  midur = hp->lodur;

  wdist = tdist = 0;
  if (hop < chopcnt && modes[hop] != Taxibit) {
    src->de_cnt++;
    // reuse previous events if equal
    if (hop == src->de_prvhop && deptmax == src->de_prvwin && tcostlim == src->de_costlim) {
      src->de_usecnt++;
      src->dcnts[1] = 0;
      src->hops[1] = hi32;
      src->nleg = 1;
      cnt = src->dcnts[0];
      if (src->hops[0] != hop) return error(Ret0,"hop %u vs %u",src->hops[0],hop);
    } else {
      cnt = mkdepevs(src,net,hop,tcostlim,dbg);
      if (cnt) {
        src->de_prvhop = hop;
        src->de_prvwin = deptmax;
        src->de_costlim = tcostlim;
      } else src->de_prvhop = hi32;
    }
  } else {
    src->de_prvhop = hi32;
    if (hop < chopcnt) bstop = 1;
    else if (hop < thopcnt) {
      bstop = 1;
      tdist = hopdist[hop];
    } else {
      wstop = 1;
      wdist = hopdist[hop];
    }
    cnt = frqevs(src,net,0,hop,nxthop,midur,walkiv_min,tcostlim);    // walk links
  }
  infocc(dbg,0,"leg 0 evs %u",cnt);
  if (cnt == 0) { return 0; }
  src->totevcnt[0] += cnt;

  curcost = src->costcurs[0];
  *pcurcost = curcost;
  if (nleg == 1) {
    src->totevcnt[0] += cnt;
    src->combicnt++;
    return cnt;
  }

  for (leg = 1; leg < nleg; leg++) {
    hop = legs[leg];
    error_ge(hop,whopcnt);
    if (hop < chopcnt) bstop++;
    else if (hop < thopcnt) {
      bstop++;
      tdist += hopdist[hop];
    } else {
      wdist += hopdist[hop];
      wstop++;
    }
  }

  ahop = legs[0];
  for (leg = 1; leg < nleg; leg++) {
    hop = legs[leg];
    midur = hops[hop].lodur;

    if (hop < chopcnt && modes[hop] != Taxibit) {
      cnt = nxtevs(src,net,leg,hop,tcostlim,dbg);
    } else { // frequency links, e.g. walk
      cnt = fwdevs(src,net,leg,ahop,hop,midur,tcostlim);
    }
    infocc(dbg,0,"leg %u hop %u evs %u",leg,hop,cnt);
    if (cnt == 0) break;
    src->totevcnt[leg] += cnt;
    ahop = hop;
  }
  src->combicnt++;
  if (cnt == 0) { return 0; }

  // apply bias wrt transfers and walk distance
  curcost = src->costcurs[nleg - 1];
  if (costperstop && bstop) {
    bstop--;
    if (curcost == hi32) ttbias = 0;
    else if (curcost < 60) ttbias = 10;
    else if (curcost < 4 * 60) ttbias = 30;
    else if (curcost < 12 * 60) ttbias =  60;
    else if (curcost < 2 * 24 * 60) ttbias = 120;
    else ttbias = 180;
    ttbias *= bstop * costperstop;
    curcost += ttbias;
    // info(Notty,"tt bias %u for %u stops",ttbias,bstop);
  } else if (bstop) {
    curcost += bstop + wstop; // minimum bias to prevent dummy transfers
  }

  if (wstop) {
    if (costperstop) curcost += costperstop * wstop * 5;
    if (wdist > 40) curcost += wdist / 20; // ~ 5 min / km
  }
  if (tdist) curcost += tdist / 100; // 5 min / 5 km
  *pcurcost = curcost;

  if (src->nleg != nleg) return error(Ret0,"nleg %u vs %u",src->nleg,nleg);

  return cnt;
#endif
}

// static, precomputed search
static ub4 srcdyn0(lnet *net,search *src,ub4 dep,ub4 arr,ub4 nleg)
{
  ub2 cnt;
  iadrbase *cnts,*ofss;
  ub8 ofs;
  ub4 *lst;
  block *lstblk;
  ub4 lodist;
  ub4 stop;
  ub4 nethistop = min(net->histop,src->nethistop);
  ub4 deptmin,deptmax;
  ub4 evcnt;
  ub4 hdist,dist = 0,leg,l;
  ub4 sumdt;
  ub4 *vp;
  ub4 curcost,costlim = src->costlim;
  ub4 *hopdist;
  ub1 txmask,mode,*modes,*mode1;
  ub4 v0;
  ub4 thopcnt = net->thopcnt;
  ub4 whopcnt = net->whopcnt;
  struct trip *stp;
  int havetime = 0,havedist = 0;
  ub4 fare;
  ub4 tdep0,tnxt;
  ub4 walklimit = src->walklimit;
  ub4 sumwalklimit = src->sumwalklimit;
  ub4 walkdist,sumwalkdist;
  char sumdesc[64];
  int dbg = 0;

  if (nleg == 0) return error0(0,"zero legcnt");
  stop = nleg - 1;
  if (stop >= Nstop) return error(0,"stop cnt %u above %u",stop,Nstop);
  lodist = src->lodist;

  if (stop > src->histop || stop > nethistop) return info(Notty,"stop limit %u/%u reached",src->histop,src->nethistop);
  if (net->lstlen[stop] == 0) return info(0,"no precomputed %u-stop net",stop);

  src->hisrcstop = max(src->hisrcstop,stop);

  src->de_prvhop = hi32;

  deptmin = src->deptmin;
  deptmax = src->deptmax;

  fmtstring(sumdesc,"s-%u",stop);

  cnts = net->concnt + stop;
  ofss = net->conofs + stop;
  lstblk = net->conlst + stop;
  modes = net->modes[stop];
  hopdist = net->hopdist;

  txmask = src->txmask;

  cnt = rdiadr2(cnts,dep,arr);

  if (cnt) {
    ofs = rdiadr8(ofss,dep,arr);
    lst = blkdata(lstblk,0,ub4);
    bound(lstblk,ofs * nleg,ub4);
    error_ge(ofs,net->lstlen[stop]);
    vp = lst + ofs * nleg;
    mode1 = modes + ofs;
  } else {
    vp = NULL;
    mode1 = NULL;
    vrb0(0,"no %u-stop connection %u-%u",stop,dep,arr);
  }

  ub8 t1,t0 = gettime_msec();

  for (v0 = 0; v0 < cnt; v0++) {

    if (timeout(FLN,src,NULL,0,0)) break;

    // distance-only
    dist = walkdist = sumwalkdist = 0;
    mode = mode1[v0];
    errorcc(mode == 0,0,"no mode for %u-stop dep %u arr %u",stop,dep,arr);
    if ((mode & txmask) != mode) { vp += nleg; continue; }
    for (leg = 0; leg < nleg; leg++) {
      l = vp[leg];
      error_ge(l,whopcnt);
      hdist = hopdist[l];
      dist += hdist;
      if (l >= thopcnt) {
        walkdist += hdist;
        sumwalkdist += hdist;
        if (walkdist > walklimit || sumwalkdist > sumwalklimit) break;
      } else walkdist = 0;
    }
    if (walkdist > walklimit || sumwalkdist > sumwalklimit) { vp += nleg; continue; }

    if (dist < lodist) {
      lodist = dist;
      src->lostop = stop;
      havedist = 1;
    }

    curcost = addevs(src,net,vp,nleg,costlim);

    if (curcost >= costlim) {
      vp += nleg;
      continue;
    }
    t1 = gettime_msec();

    msgprefix(0,"d0 %u-x-x %u",nleg,curcost);

    info(0,"curcost %u costlim %u dist %u lodist %u",curcost,costlim,dist,lodist);
    costlim = curcost;
    srcinfo(src,0,nleg,0,0,0,v0,cnt,t1 - t0);

    havetime = 1;

#if 0
    evcnt = getevs(src,net,nleg,vp,0,"dyn0");
    if (evcnt == 0) { vp += nleg; continue; }

    stp = setrip(src,net,curcost,&costlim,nleg,vp,"dyn0");
    if (stp == NULL) return 0;

    stp->dist = dist;
    sumdt = stp->dt;
    fare = stp->fare;

    if (dist < src->lodist) src->lodist = dist;

    tdep0 = src->curts[0];
    evcnt = getevs(src,net,nleg,vp,1,"dyn0");
    if (evcnt) tnxt = max(src->curts[0],tdep0) - tdep0;
    else tnxt = hi32;
    fmtstring(sumdesc,"dyn0 %u/%s at %lu ms",nleg,src->dwinfo,t1 - t0);
    fmtsum(FLN,stp,sumdt,tnxt,dist,fare,curcost,sumdesc);
    info(0,"found \av%u%p win %u t %lu %s",nleg,(void *)vp,src->dephwin,t1 - t0,stp->desc);
#endif

    src->timestop = min(src->timestop,stop);

    vp += nleg;
  } // each v0

  if (havetime) {
    info(V0,"found %u-stop conn %u-%u",stop,dep,arr);
    return 1;
  }

  info(V0,"no time for %u-stop trip %u-%u on \ad%u-\ad%u",stop,dep,arr,deptmin,deptmax);

  if (havedist == 0) info(V0,"no route for %u-stop trip %u-%u",stop,dep,arr);

  return havetime;
}

static int portintrip(ub4 dep,ub4 *ports,ub4 nport)
{
  ub4 i;
  for (i = 0; i < nport; i++) if (dep == ports[i]) return 1;
  return 0;
}

// dynamic search for one extra stop
static int srcdyn1(lnet *net,struct srcplan *sp,search *src,ub4 dep,ub4 arr,ub4 nleg1,ub4 nleg2)
{
  struct port *pdep,*pmid,*parr,*ports = net->ports;
  struct chop *hp2,*hops = net->chops;
  ub4 portcnt = net->portcnt;
  ub4 thopcnt = net->thopcnt;
  ub4 *hopdist = net->hopdist;
  ub4 *portsbyhop = net->portsbyhop;
  ub1 mode,txmask,*modes1,*modes2,*mode1,*mode2;
  ub4 mid,dep1,dep2,dmid,ddmid,sdmid;
  ub8 ofs1,ofs2;
  ub4 leg1,leg2,n1,n2,v1,v2;
  ub4 rid1;
  iadrbase *cnts1,*cnts2;
  iadrbase *conofs1,*conofs2;
  block *lstblk1,*lstblk2;
  ub4 *conlst1,*conlst2,*lst1,*lst2,*lst11,*lst22;
  ub4 sumdt;
  ub4 fare;
  ub4 curcost,costlim;
  ub4 evcnt;
  ub4 trip[Nleg];
  ub4 ptrip[Nleg+1];
  struct trip *stp;
  ub4 nleg,stop,stop1,stop2;
  ub4 hop1,hop2;
  ub4 dist,hdist,dist1,dist2,walkdist1,sumwalkdist1,walkdist2,sumwalkdist2;
  ub4 nethistop = min(net->histop,src->nethistop);
  ub4 nethileg = nethistop + 1;

  ub4 deptmin = src->deptmin;
  ub4 deptmax = src->deptmax;
  ub4 walklimit = src->walklimit;
  ub4 sumwalklimit = src->sumwalklimit;

  ub4 lodist = src->lodist;
  int havetime = 0;
  ub4 tdep0,tnxt;
  char sumdesc[64];
  int dbg = 0;

  ub4 stat_portdup = 0,stat_varcnt = 0,stat_evcnt = 0;

  pdep = ports + dep;
  parr = ports + arr;
  if (pdep->valid == 0) return info(0,"dep %u not valid",dep);
  if (parr->valid == 0) return info(0,"arr %u not valid",arr);

  curcost = hi32;
  costlim = src->costlim;

  src->de_prvhop = hi32;

  stp = src->trips;

  if (nleg1 == 0 || nleg2 == 0) return info0(0,"no dyn1 on 0-leg");
  stop1 = nleg1 - 1;
  stop2 = nleg2 - 1;
  nleg = nleg1 + nleg2;
  stop = nleg - 1;
  if (stop >= Nstop) return error(0,"stop cnt %u above %u",stop,Nstop);

  if (nleg1 > nethileg) return info(0,"ending dyn1 %u-stop search on %u-stop precomputed net",nleg1,nethistop);
  if (nleg2 > nethileg) return info(0,"ending dyn1 %u-stop search on %u-stop precomputed net",nleg2,nethistop);

  if (net->lstlen[stop1] == 0) return info(0,"no precomputed %u-stop net",stop1);
  if (net->lstlen[stop2] == 0) return info(0,"no precomputed %u-stop net",stop2);

  ub4 *dlst,*deplst = net->deplst[stop1];
  ub4 *dlstdur,*depdurlst = net->depdurlst[stop1];

  txmask = src->txmask;

  dep1 = dep2 = hi32;

  fmtstring(sumdesc,"dyn1 %u+%u",nleg1,nleg2);

  cnts1 = net->concnt + stop1;
  cnts2 = net->concnt + stop2;

  if (cnts1->state == 0) return warn(0,"ending %u-stop search on %u-stop precomputed net",stop1,nethistop);
  if (cnts2->state == 0) return warn(0,"ending %u-stop search on %u-stop precomputed net",stop2,nethistop);

  src->hisrcstop = max(src->hisrcstop,stop);

  lstblk1 = net->conlst + stop1;
  lstblk2 = net->conlst + stop2;

  conlst1 = blkdata(lstblk1,0,ub4);
  conlst2 = blkdata(lstblk2,0,ub4);

  conofs1 = net->conofs + stop1;
  conofs2 = net->conofs + stop2;

  modes1 = net->modes[stop1];
  modes2 = net->modes[stop2];

  hop1 = 0;

  ub8 t1,t0 = gettime_msec();

  ub8 x8,dmidsort[Dyn1_midlim];
  ub4 depcnt = pdep->depcnt[stop1];
  ub4 depofs = pdep->depofs[stop1];
  if (depofs >= net->pairs[stop1]) {
    error(Exit,"net %u dep %u ofs %u cnt %u above %lu",stop1,dep,depofs,depcnt,net->pairs[stop1]);
    return 0;
  }
  if (depofs + depcnt > net->pairs[stop1]) {
    error(Exit,"net %u dep %u ofs %u cnt %u above %lu",stop1,dep,depofs,depcnt,net->pairs[stop1]);
    return 0;
  }
  dlst = deplst + depofs;
  dlstdur = depdurlst + depofs;

  ub4 dmidcnt = 0;

  ub4 dur,durdist;
  ub4 dirdistm1a,dirdist = fgeodist(pdep,parr,1);
  ub4 gdistlim = geodistlim(dirdist);

  ub4 seq1;
  ub4 gseqcnt = net->seqdlen;
  ub2 *seqdist = net->seqdist;

  // sort via
  ub4 sdepcnt = 0;
  for (dmid = 0; dmid < depcnt && sdepcnt < Dyn1_midlim; dmid++) {
    ddmid = dlst[dmid];
    mid = ddmid & Nbrmask;
    if ( (ddmid & Viabit) == 0 && (ddmid & Tripbits) != Tripbits ) continue;

    if (mid == arr) continue;

    pmid = ports + mid;

    seq1 = pmid->gridseq;

    dirdistm1a = xgeodist(pmid,parr,seq1,gseqcnt,seqdist);

    if (dirdistm1a > gdistlim) continue;

    dur = dlstdur[dmid];
    if (stop1 == 0 && dur >= costlim) continue;
    if (costlim != hi32 && dur > costlim * 2) continue;

    durdist = dirdistm1a + dur * 50;
    dmidsort[sdepcnt++] = ((ub8)durdist << 32) | mid;
  }
  if (sdepcnt == Dyn1_midlim) src->midlim1cnt++;
  if (sdepcnt > 1 && sp->sort) fsort8(dmidsort,sdepcnt,0,FLN,"dmid");
  else if (sdepcnt == 0) return info(0,"0 from %u mid1",depcnt);

  // each via
  for (sdmid = 0; sdmid < sdepcnt; sdmid++) {
    x8 = dmidsort[sdmid];
    dirdistm1a = (ub4)(x8 >> 32);
    mid = x8 & hi32;
    error_ge(mid,portcnt);

    pmid = ports + mid;

    if (timeout(FLN,src,sp,sdmid,sdepcnt)) {
      info(0,"vars %u evs %u",stat_varcnt,stat_evcnt);
      return havetime;
    }

    n1 = rdiadr2(cnts1,dep,mid);
    if (n1 == 0) {
      info(0,"dep %u arr %u cnt 0/%u",dep,mid,depcnt);
      continue;
    }

    n2 = rdiadr2(cnts2,mid,arr);
    if (n2 == 0) continue;

    dmidcnt++;

    infocc(dbg,0,"n1 %u n2 %u",n1,n2);

    ofs1 = rdiadr8(conofs1,dep,mid);
    ofs2 = rdiadr8(conofs2,mid,arr);

    lst1 = conlst1 + ofs1 * nleg1;
    lst2 = conlst2 + ofs2 * nleg2;

    mode1 = modes1 + ofs1;
    mode2 = modes2 + ofs2;

    for (v1 = 0; v1 < n1; v1++) {
      lst11 = lst1 + v1 * nleg1;
      mode = mode1[v1];
      errorcc(mode == 0,0,"no mode for %u-stop dep %u arr %u",stop1,dep,arr);
      if ((mode & txmask) != mode) continue;
      dist1 = walkdist1 = sumwalkdist1 = 0;
      for (leg1 = 0; leg1 < nleg1; leg1++) {
        hop1 = lst11[leg1];
        if (leg1) {
          dep1 = portsbyhop[hop1 * 2];
          if (dep1 == arr) { stat_portdup++; break; }
          ptrip[leg1] = dep1;
        }
        hdist = hopdist[hop1];
        dist1 += hdist;
        if (hop1 >= thopcnt) {
          walkdist1 += hdist;
          sumwalkdist1 += hdist;
          if (walkdist1 > walklimit) break;
        } else walkdist1 = 0;
        trip[leg1] = hop1;
      }
      if (leg1 != nleg1) continue;
      if (sumwalkdist1 > sumwalklimit) continue;

      rid1 = hops[hop1].rid;

      for (v2 = 0; v2 < n2; v2++) {
        lst22 = lst2 + v2 * nleg2;
        mode = mode2[v2];
        if ((mode & txmask) != mode) continue;

        dist2 = dist1;
        walkdist2 = walkdist1;
        sumwalkdist2 = sumwalkdist1;

        hop2 = lst22[0];
        if (hop2 >= thopcnt && hop1 >= thopcnt) continue; // walk after walk

        hp2 = hops + hop2;
        if (rid1 == hp2->rid && hp2->tripstart == 0) continue;

        for (leg2 = 0; leg2 < nleg2; leg2++) {
          hop2 = lst22[leg2];
          if (leg2) {
            dep2 = portsbyhop[hop2 * 2];
            if (nleg1 > 1 && portintrip(dep2,ptrip+1,nleg1-1)) { stat_portdup++; break; }
          }
          hdist = hopdist[hop2];
          dist2 += hdist;
          if (hop2 >= thopcnt) {
            walkdist2 += hdist;
            sumwalkdist2 += hdist;
            if (walkdist2 > walklimit) break;
          } else walkdist2 = 0;
          trip[nleg1 + leg2] = hop2;
        }
        if (leg2 != nleg2) continue;
        if (sumwalkdist2 > sumwalklimit) continue;

        dist = dist2;

        if (dist < lodist) { // route-only
          if (checktrip3(net,trip,nleg,dep,arr,mid,hi32)) continue; // todo
          lodist = src->lodist = dist;
          info(V0,"find route-only at dist %u",lodist);
        }

        stat_varcnt++;

        curcost = addevs(src,net,trip,nleg,costlim);
        stp = src->trips;

        if (curcost >= costlim) {
          // info(Notty,"%u legs %u event\as cost %u win %u",nleg,evcnt,curcost,src->dephwin);
          continue;
        }
        t1 = gettime_msec();

        msgprefix(0,"d1 %u-%u-x %u",nleg1,nleg2,curcost);

        info(0,"cost %u from %u",curcost,costlim);
        havetime = 1;
        costlim = curcost;

        srcinfo(src,1,nleg1,nleg2,0,0,sdmid,sdepcnt,t1 - t0);

        if (checktrip3(net,trip,nleg,dep,arr,mid,hi32)) continue;

#if 0
        evcnt = getevs(src,net,nleg,trip,0,"dyn1");
        if (evcnt == 0) continue;

        infocc(evcnt,V0,"%u legs %u event\as cost %u \at%u win %u",nleg,evcnt,curcost,curcost,src->dephwin);

        stp = setrip(src,net,curcost,&costlim,nleg,trip,"dyn1");
        if (stp == NULL) return 1;

        havetime = 1;
        fare = stp->fare;
        sumdt = stp->dt;
        stp->dist = dist;

        if (dist < src->lodist) src->lodist = dist;
        src->costlim = costlim;

        tdep0 = src->curts[0];
        evcnt = getevs(src,net,nleg,trip,1,"dyn1");
        if (evcnt) tnxt = max(src->curts[0],tdep0) - tdep0;
        else tnxt = hi32;
        t1 = gettime_msec();
        fmtstring(sumdesc,"dyn1 %u+%u/%s at %lu ms",nleg1,nleg2,src->dwinfo,t1 - t0);
        fmtsum(FLN,stp,sumdt,tnxt,dist,fare,curcost,sumdesc);
#endif
        info(0,"found \av%u%p win %u t %lu",nleg,(void *)trip,src->dephwin,t1 - t0);
        src->timestop = min(src->timestop,stop);
      } // each v2
    } // each v1

  } // each mid

  if (havetime) {
    info(V0,"found %u-stop conn %u-%u cost %u dups \ah%u",stop,dep,arr,curcost,stat_portdup);
    return info(Ret1,"mids %u/%u vars %u evs %u",dmidcnt,sdepcnt,stat_varcnt,stat_evcnt);
  }

  info(V0,"no time for %u-stop trip %u-%u on \ad%u-\ad%u dups \ah%u",stop,dep,arr,deptmin,deptmax,stat_portdup);
  return info(0,"mids %u/%u vars %u evs %u",dmidcnt,sdepcnt,stat_varcnt,stat_evcnt);
} // dyn1

// dynamic search for one or more extra stops, using 2 vias
static int srcdyn2(lnet *net,search *src,struct srcplan *sp,
                   ub4 dep,ub4 arr,
                   ub4 nleg1,ub4 nleg2,ub4 nleg3,
                   ub4 dmid1cnt,ub4 *dmid1s,ub4 *dmid1durs,
                   ub4 dmid2cnt,ub4 *dmid2s,ub4 *dmid2durs,ub4 *dmid2ns)
{
  ub4 portcnt = net->portcnt;
  ub4 thopcnt = net->thopcnt;
  ub4 *hopdist = net->hopdist;
  ub4 lodur;
  ub4 *portsbyhop = net->portsbyhop;
  ub1 txmask,mode,*modes1,*modes2,*modes3,*mode1,*mode2,*mode3;
  struct port *pdep,*parr,*ports = net->ports;
  struct chop *hp2,*hp3,*hops = net->chops;
  ub4 stop1,stop2,stop3,stop;
  ub4 mid1,mid2,dep1,dep2,dep3;
  ub8 ofs1,ofs2,ofs3;
  ub4 leg1,leg2,leg3,n1,n2,n3,v1,v2,v3;
  ub4 rid1;
  iadrbase *conofs1,*conofs2,*conofs3;
  iadrbase *cnts1,*cnts2,*cnts3;
  block *lstblk1,*lstblk2,*lstblk3;
  ub4 *conlst1,*conlst2,*conlst3,*lst1,*lst2,*lst3,*lst11,*lst22,*lst33;
  ub4 sumdt;
  ub4 evcnt;
  ub4 trip[Nleg];
  ub4 ptrip[Nleg+1];
  struct trip *stp;
  ub4 nleg;
  ub4 h1,h2,h3;
  ub4 dist,hdist,dist1,dist2,dist3,walkdist1,sumwalkdist1,walkdist2,sumwalkdist2,walkdist3,sumwalkdist3;
  ub4 nethistop = min(net->histop,src->nethistop);

  ub4 deptmin = src->deptmin;
  ub4 deptmax = src->deptmax;
  ub4 walklimit = src->walklimit;
  ub4 sumwalklimit = src->sumwalklimit;
  ub4 tdep0,tnxt;

  ub4 lodist = src->lodist;
  ub4 curcost,costlim = src->costlim;
  int havetime = 0;
  ub4 fare;
  ub4 altcnt;
  char sumdesc[64];
  int dbg = 0;

  pdep = ports + dep;
  if (pdep->valid == 0) return 0;
  parr = ports + arr;
  if (parr->valid == 0) return 0;

  src->de_prvhop = hi32;

  error_z(nleg1,dep);
  error_z(nleg2,dep);
  error_z(nleg3,dep);

  stop1 = nleg1 - 1;
  stop2 = nleg2 - 1;
  stop3 = nleg3 - 1;
  if (stop1 > nethistop || stop2 > nethistop || stop3 > nethistop) {
    return info(0,"legs %u,%u,%u not in precomputed %u",nleg1,nleg2,nleg3,nethistop);
  }

  if (stop1 >= Netn || stop2 >= Netn || stop3 >= Netn) return 0;

  if (net->lstlen[stop1] == 0) return info(0,"no precomputed %u-stop net",stop1);
  if (net->lstlen[stop2] == 0) return info(0,"no precomputed %u-stop net",stop2);
  if (net->lstlen[stop3] == 0) return info(0,"no precomputed %u-stop net",stop3);

  stp = src->trips;

  txmask = src->txmask;

  dep1 = dep2 = dep3 = hi32;

  nleg = nleg1 + nleg2 + nleg3;
  if (nleg >= Nleg) return info(0,"skip on legcnt %u above max %u",nleg,Nleg);
  stop = nleg - 1;
  if (stop >= Nstop) return error(0,"stop cnt %u above %u",stop,Nstop);

  cnts1 = net->concnt + stop1;
  cnts2 = net->concnt + stop2;
  cnts3 = net->concnt + stop3;

  if ( (cnts1->state | cnts2->state | cnts3->state) == 0) return 0;

  iadrbase *cntsn1 = nethistop && net->lstlen[1] ? net->concnt + 1 : NULL;
  iadrbase *cntsn2 = nethistop > 1 && net->lstlen[2] ? net->concnt + 2 : NULL;
  iadrbase *cntsn3 = nethistop > 2 && net->lstlen[3] ? net->concnt + 3 : NULL;

  if (cnts1->state == 0 || cnts2->state == 0 || cnts3->state == 0) return info0(0,"dyn2 net not inited");
  if (cntsn1 && cntsn1->state == 0) return info0(0,"dyn2 net1 not inited");
  if (cntsn2 && cntsn2->state == 0) return info0(0,"dyn2 net2 not inited");
  if (cntsn3 && cntsn3->state == 0) return info0(0,"dyn2 net3 not inited");

  src->hisrcstop = max(src->hisrcstop,nleg - 1);

  fmtstring(sumdesc,"dyn2 %u+%u+%u",nleg1,nleg2,nleg3);

  lstblk1 = net->conlst + stop1;
  lstblk2 = net->conlst + stop2;
  lstblk3 = net->conlst + stop3;

  conlst1 = blkdata(lstblk1,0,ub4);
  conlst2 = blkdata(lstblk2,0,ub4);
  conlst3 = blkdata(lstblk3,0,ub4);

  conofs1 = net->conofs + stop1;
  conofs2 = net->conofs + stop2;
  conofs3 = net->conofs + stop3;

  modes1 = net->modes[stop1];
  modes2 = net->modes[stop2];
  modes3 = net->modes[stop3];

  error_zp(modes1,stop1);
  error_zp(modes2,stop2);
  error_zp(modes3,stop3);

  ub4 dmid1,dmid2;

  ub4 varcnt = 0;
  h1 = 0;
  ub4 stat_portdup = 0;

  ub8 t1,t0 = gettime_msec();

  ub4 depcnt = pdep->depcnt[stop1];
  ub4 depofs = pdep->depofs[stop1];
  error_gt(depofs + depcnt,net->pairs[stop1],dep);
  ub4 dur1,dur2;

  // each mid1
  for (dmid1 = 0; dmid1 < dmid1cnt; dmid1++) {
    mid1 = dmid1s[dmid1];
    if (mid1 == arr) continue;

    dur1 = dmid1durs[dmid1];

    if (stop1 == 0 && dur1 >= costlim) continue;
    if (costlim != hi32 && dur1 > costlim * 2) continue;

    if (timeout(FLN,src,sp,dmid1,dmid1cnt)) return havetime;

    ? n1 = rdiadr2(cnts1,dep,mid1);
    if (n1 == 0) continue;

    n1 = min(n1,var1lim2);

    sort conlst on dep and arr ?
    bsearch for larger cnt
    // each via2
    for (dmid2 = 0; dmid2 < dmid2cnt; dmid2++) {
      mid2 = dmid2s[dmid2];
      if (mid2 == mid1) continue;

      dur2 = dmid2durs[dmid2];

      if (stop1 == 0 && stop3 == 0 && dur1 + dur2 >= costlim) continue;
      if (costlim != hi32 && dur1 + dur2 > costlim * 2) continue;

      error_ge_cc(mid2,portcnt,"dmid2 %u/%u",dmid2,dmid2cnt);

      if (timeout(FLN,src,sp,dmid1,dmid1cnt)) return havetime;

      n2 = rdiadr2(cnts2,mid1,mid2);
      if (n2 == 0) continue;

      n2 = min(n2,var1lim2);

      n3 = dmid2ns[dmid2];

      ofs1 = rdiadr8(conofs1,dep,mid1);
      ofs2 = rdiadr8(conofs2,mid1,mid2);
      ofs3 = rdiadr8(conofs3,mid2,arr);

      lst1 = conlst1 + ofs1 * nleg1;
      lst2 = conlst2 + ofs2 * nleg2;
      lst3 = conlst3 + ofs3 * nleg3;

      mode1 = modes1 + ofs1;
      mode2 = modes2 + ofs2;
      mode3 = modes3 + ofs3;

      altcnt = 0;

      // infocc(dbg,0,"mid1 %u:%u mid2 %u:%u",mid1,n1,mid2,n2);

      for (v1 = 0; v1 < n1; v1++) {

        if (altcnt > altlimit2) break;
        mode = mode1[v1];
        if ((mode & txmask) != mode) continue;
        lst11 = lst1 + v1 * nleg1;

        dist1 = walkdist1 = sumwalkdist1 = 0;
        lodur = 0;
        for (leg1 = 0; leg1 < nleg1; leg1++) {
          h1 = lst11[leg1];
          if (leg1) {
            dep1 = portsbyhop[h1 * 2];
            if (dep1 == arr || dep1 == mid2) break;
            ptrip[leg1] = dep1;
          }
          hdist = hopdist[h1];
          dist1 += hdist;
          lodur += hops[h1].lodur;
          if (h1 >= thopcnt) {
            walkdist1 += hdist;
            sumwalkdist1 += hdist;
            if (walkdist1 > walklimit) break;
          } else walkdist1 = 0;
          trip[leg1] = h1;
        }
        if (leg1 != nleg1) continue;
        if (sumwalkdist1 > sumwalklimit) continue;

        if (lodist != hi32 && dist1 > 10 * lodist) { continue; }
        if (lodur > costlim) continue;

        rid1 = hops[h1].rid;

        for (v2 = 0; v2 < n2; v2++) {
          if (altcnt > altlimit2) break;
          mode = mode2[v2];
          if ((mode & txmask) != mode) continue;

          lst22 = lst2 + v2 * nleg2;

          dist2 = dist1;
          walkdist2 = walkdist1;
          sumwalkdist2 = sumwalkdist1;

          h2 = lst22[0];
          if (h2 >= thopcnt && h1 >= thopcnt) continue; // walk after walk

          hp2 = hops + h2;
          if (rid1 == hp2->rid && hp2->tripstart == 0) continue;

          for (leg2 = 0; leg2 < nleg2; leg2++) {
            h2 = lst22[leg2];

            if (leg2) {
              dep2 = portsbyhop[h2 * 2];
              if (dep2 == arr || dep2 == dep) break;
              if (nleg1 > 1 && portintrip(dep2,ptrip+1,nleg1-1)) { stat_portdup++; break; }
            }
            hdist = hopdist[h2];
            dist2 += hdist;
            lodur += hops[h2].lodur;
            if (h2 >= thopcnt) {
              walkdist2 += hdist;
              sumwalkdist2 += hdist;
              if (walkdist2 > walklimit) break;
            } else walkdist2 = 0;
            trip[nleg1 + leg2] = h2;
            ptrip[nleg1 + leg2] = dep2;
          }
          if (sumwalkdist2 > sumwalklimit) continue;
          if (leg2 != nleg2) continue;

          if (lodist != hi32 && dist2 > 10 * lodist) { continue; }
          if (lodur > costlim) continue;

          for (v3 = 0; v3 < n3; v3++) {
            if (altcnt > altlimit2) break;

            mode = mode3[v3];
            if ((mode & txmask) != mode) continue;

            lst33 = lst3 + v3 * nleg3;

            dist3 = dist2;
            walkdist3 = walkdist2;
            sumwalkdist3 = sumwalkdist2;

            h3 = lst33[0];
            if (h3 >= thopcnt && h2 >= thopcnt) continue;
            hp3 = hops + h3;
            if (hp2->rid == hp3->rid && (hp2->tripend == 0 || hp3->tripstart == 0)) continue;

            for (leg3 = 0; leg3 < nleg3; leg3++) {
              h3 = lst33[leg3];
              if (leg3) {
                dep3 = portsbyhop[h3 * 2];
                if (dep3 == mid1 || dep3 == dep) { stat_portdup++; break; }
                if (portintrip(dep3,ptrip+1,nleg1+nleg2-1)) { stat_portdup++; break; }
              }
              hdist = hopdist[h3];
              dist3 += hdist;
              if (h3 >= thopcnt) {
                walkdist3 += hdist;
                sumwalkdist3 += hdist;
                if (walkdist3 > walklimit) break;
              } else walkdist3 = 0;
              trip[nleg1 + nleg2 + leg3] = h3;
            }
            if (leg3 != nleg3) continue;
            if (sumwalkdist3 > sumwalklimit) continue;

            if (lodist != hi32 && dist3 > 10 * lodist) { continue; }

            altcnt++;
            if (altcnt == altlimit2 / 2) src->stat_altlim2++;

            // infocc(dbg,Noiter,"trip %u-%u-%u n %u-%u-%u = %u",h1,h2,h3,n1,n2,n3,altcnt);

            dist = dist3;
            if (dist < lodist) { // route-only
              if (checktrip3(net,trip,nleg,dep,arr,mid1,hi32)) continue;
              if (checktrip3(net,trip,nleg,dep,arr,mid2,hi32)) continue;
              info(V0,"find route-only at dist %u",dist);
              lodist = src->lodist = dist;
            }

            curcost = addevs(src,net,trip,nleg,costlim);
            if (costlim <= curcost) continue;

            t1 = gettime_msec();

            msgprefix(0,"d2 %u-%u-%u %u",nleg1,nleg2,nleg3,curcost);

            if (checktrip3(net,trip,nleg,dep,arr,mid1,hi32)) continue;
            if (checktrip3(net,trip,nleg,dep,arr,mid2,hi32)) continue;

            infocc(dbg,Notty,"%u legs curcost %u costlim %u win %u",nleg,curcost,costlim,src->dephwin);

            costlim = curcost;
            havetime = 1;
            srcinfo(src,2,nleg1,nleg2,nleg3,0,dmid1,dmid1cnt,t1 - t0);

#if 0
            evcnt = getevs(src,net,nleg,trip,0,"dyn2");
            if (evcnt == 0) continue;

            stp = setrip(src,net,curcost,&costlim,nleg,trip,"dyn2");
            if (stp == NULL) return 1;

            havetime = 1;
            sumdt = stp->dt;
            fare = stp->fare;
            stp->dist = dist;

            if (dist < src->lodist) src->lodist = dist;
            costlim = costlim;

            src->timestop = min(src->timestop,nleg - 1);

            tdep0 = src->curts[0];
            evcnt = getevs(src,net,nleg,trip,1,"dyn2");
            if (evcnt) tnxt = max(src->curts[0],tdep0) - tdep0;
            else tnxt = hi32;

            t1 = gettime_msec();
            fmtstring(sumdesc,"dyn2 %u+%u+%u/%s at %lu ms",nleg1,nleg2,nleg3,src->dwinfo,t1 - t0);
            fmtsum(FLN,stp,sumdt,tnxt,dist,fare,curcost,sumdesc);
#endif
            src->timestop = min(src->timestop,stop);
            // info(0,"found \av%u%p win %u t %lu",nleg,(void *)trip,src->dephwin,t1 - t0);

            src->dyn2stat[stop3 * Netn * Netn + stop2 * Netn + stop1]++;

          } // each v3
        } // each v2
      } // each v1
  //    infocc(altcnt == altlimit2 / 2,Notty,"%u of max %u alts",altcnt,altlimit2)

    varcnt += altcnt;
    } // each mid2
  } // each mid1

  info(0,"\ah%u var\as \ah%u dup\as",varcnt,stat_portdup);

  if (havetime) return 1;

  info(V0,"no time for %u-stop trip %u-%u on \ad%u-\ad%u",nleg-1,dep,arr,deptmin,deptmax);
  src->lodist = lodist;

  return 0;
} // dyn2

// dynamic search for one or more extra stops, using 2 vias
static int srcdyn2_var(lnet *net,search *src,ub4 dep,ub4 arr,struct srcplan *plan,ub4 costndx,ub4 *ptxtra,ub4 *phindx)
{
  ub4 nleg,nleg1,nleg2,nleg3;
  ub4 loleg1 = hi32,loleg2 = hi32,loleg3 = hi32;
  ub4 hileg1 = 0,hileg2 = 0,hileg3 = 0;
  ub4 histop1,histop2,histop3;
  ub4 n3;
  char desc[256];
  struct srcplan *pp,*ppend,*pp2;
  ub4 portcnt = net->portcnt;
  struct port *pdep,*parr,*pmid1,*pmid2,*ports = net->ports;
  ub4 stop1,stop2,stop3;
  ub4 mid1,mid2;
  iadrbase *cnts1,*cnts3;

  ub4 nethistop = min(net->histop,src->nethistop);
  ub4 nethileg = nethistop + 1;
  ub4 tx,txtra = *ptxtra;
  ub4 hindx = hi32,hiuse = 0;

  if (nethistop >= Netn) return error(Ret0,"histop %u above %u",nethistop,Netn);

  int rv = 0;

  pdep = ports + dep;
  if (pdep->valid == 0) return 0;
  parr = ports + arr;
  if (parr->valid == 0) return 0;

  pp2 = plan + costndx;
  ub4 planlen = costndx;

  // get leg ranges
  pp = pp2;
  while (pp->nleg1 && pp->nleg4 == 0) {
    planlen++;
    if (planlen >= Planlen) {
      warn(0,"plan unterminated at %u from %u",planlen,costndx);
      pp->nleg1 = 0;
      break;
    }
    if (pp->tlim == 0 || pp->run == 0) { pp++; continue; }
    nleg1 = pp->nleg1;
    nleg2 = pp->nleg2;
    nleg3 = pp->nleg3;
    error_z(nleg2,costndx);
    error_z(nleg3,costndx);
    nleg = nleg1 + nleg2 + nleg3;
    if (nleg >= Nleg) return error(Ret0,"legcnt %u above max %u",nleg,Nleg);
    if (nleg1 > nethileg || nleg2 > nethileg || nleg3 > nethileg) { pp++; continue; }
    loleg1 = min(loleg1,nleg1);
    loleg2 = min(loleg2,nleg2);
    loleg3 = min(loleg3,nleg3);
    hileg1 = max(hileg1,nleg1);
    hileg2 = max(hileg2,nleg2);
    hileg3 = max(hileg3,nleg3);
    pp++;
  }
  ppend = pp;

  if (loleg1 == 0 || loleg2 == 0 || loleg3 == 0) return info(0,"dyn2: zero legs at pos %u",pp->ndx);
  if (hileg1 == 0 || hileg2 == 0 || hileg3 == 0) return info(0,"dyn2: zero legs at pos %u",pp->ndx);
  histop1 = hileg1 - 1;
  histop2 = hileg2 - 1;
  histop3 = hileg3 - 1;

  if (histop1 > nethistop || histop2 > nethistop || histop3 > nethistop) {
    return error(Ret0,"legs %u,%u,%u not in precomputed %u",hileg1,hileg2,hileg3,nethistop);
  }

  info(V0,"%u-%u %u-%u %u-%u",loleg1,hileg1,loleg2,hileg2,loleg3,hileg3);

  ub4 *dlst,*deplst,*alst,*arrlst;
  ub4 *dlstdur,*depdurlst;
  ub4 *alstdur,*arrdurlst;

  ub8 x8,dmid1sort[Dyn2_midlim];
  ub4 dmid2lim = min(portcnt,Dyn2_midlim);
  ub4 dmid1,xdmid1,dmid1cnt,dmid2,dmid2cnt = 0;

  ub4 *dmid1s,sdmid1s[Dyn2_midlim * Netn];
  ub4 *dmid2s,sdmid2s[Dyn2_midlim * Netn];

  ub4 *dmid2ns,sdmid2ns[Dyn2_midlim * Netn];

  ub4 *dmid1durs,sdmid1durs[Dyn2_midlim * Netn];
  ub4 *dmid2durs,sdmid2durs[Dyn2_midlim * Netn];

  ub4 dmid1cnts[Netn];
  ub4 dmid2cnts[Netn];
  ub4 org1cnts[Netn];
  ub4 org2cnts[Netn];

  ub4 sdepcnt;
  ub8 pairs;

  ub4 dirdistm1a,dirdistdm2,dirdist = src->geodist;
  ub4 gdistlim = geodistlim(dirdist);

  ub4 seq1,seqdep = pdep->gridseq;
  ub4 gseqcnt = net->seqdlen;
  ub2 *seqdist = net->seqdist;

  ub4 depcnt,depofs;
  ub4 dur,durdist;

  ub4 darr,ddmid,ddarr,arrcnt;
  ub4 arrofs;

  ub4 hidmid1cnt = 0,hidmid2cnt = 0;

  ub4 curcost = src->costlim;
  int xview = (src->srcmode == Srcxtime);

  error_ge(histop3,Nstop-1);

// prepare mid2s
  aclear(dmid2cnts);
  for (stop3 = loleg3 - 1; stop3 <= histop3; stop3++) {

    if (stop3 >= Netn) return error(Ret0,"n-stop %u above %u",stop3,Netn);

    if (net->lstlen[stop3] == 0) continue;

    dmid2 = 0;
    dmid2s = sdmid2s + stop3 * Dyn2_midlim;
    dmid2ns = sdmid2ns + stop3 * Dyn2_midlim;
    dmid2durs = sdmid2durs + stop3 * Dyn2_midlim;

    arrlst = net->arrlst[stop3];
    arrdurlst = net->arrdurlst[stop3];

    arrcnt = parr->arrcnt[stop3];
    arrofs = parr->arrofs[stop3];

    if (arrcnt == 0) continue;

    cnts3 = net->concnt + stop3;

    alst = arrlst + arrofs;
    alstdur = arrdurlst + arrofs;

    error_ge(arrcnt,portcnt);
    pairs = net->pairs[stop3];
    if (arrofs >= pairs) {
      error(Exit,"net %u port %u ofs %u not in %lu",stop3,arr,arrofs,pairs);
      break;
    }
    if (arrofs + arrcnt > pairs) {
      error(Exit,"net %u port %u ofs %u+%u not in %lu",stop3,arr,arrofs,arrcnt,pairs);
      break;
    }
    dmid2 = 0;

    for (darr = 0; darr < arrcnt && dmid2 < dmid2lim; darr++) {
      ddarr = alst[darr];
      mid2 = ddarr & Nbrmask;

      error_ge_cc(mid2,portcnt,"darr %u/%u arr %u ofs %u",darr,arrcnt,arr,arrofs);

      if ( (ddarr & Viabit) == 0 && (ddarr & Tripbits) != Tripbits ) continue;
      if (mid2 == dep) continue;

      pmid2 = ports + mid2;

      dirdistdm2 = xgeodist(pdep,pmid2,seqdep,gseqcnt,seqdist);

      if (dirdistdm2 > gdistlim) continue;

      dur = alstdur[darr];

      if (xview) {
        if (stop3 == 0 && dur >= curcost) continue;
        if (curcost != hi32 && dur > curcost * 2) continue;
      }

      dmid2durs[dmid2] = dur;
      dmid2s[dmid2] = mid2;

      n3 = rdiadr2(cnts3,mid2,arr);
      if (n3 == 0) {
        warn(0,"dep %u arr %u cnt 0/%u net %u at %u",mid2,arr,arrcnt,stop3,arrofs + darr);
        continue;
      }

      n3 = min(n3,var1lim2);

      dmid2ns[dmid2++] = n3;

    }
    dmid2cnt = dmid2;
    if (dmid2cnt == dmid2lim) src->mid2limcnt2++;
    vrb(0,"%u-stop %u from %u mid2s",stop3,dmid2,arrcnt);
    if (dmid2cnt == 0) continue;
    dmid2cnts[stop3] = dmid2cnt;
    org2cnts[stop3] = arrcnt;
    hidmid2cnt = max(hidmid2cnt,dmid2cnt);
  }
  if (hidmid2cnt == 0) return 0;

// prepare mid1s
  aclear(dmid1cnts);
  for (stop1 = loleg1 - 1; stop1 <= histop1; stop1++) {

    if (stop1 >= Netn) return error(Ret0,"n-stop %u above %u",stop1,Netn);

    if (net->lstlen[stop1] == 0) continue;

    dmid1 = 0;
    dmid1s = sdmid1s + stop1 * Dyn2_midlim;
    dmid1durs = sdmid1durs + stop1 * Dyn2_midlim;

    deplst = net->deplst[stop1];
    depdurlst = net->depdurlst[stop1];

    cnts1 = net->concnt + stop1;

    if (cnts1->state == 0) {
      info(0,"dyn2 %s net not inited",desc);
      continue;
    }

    depcnt = pdep->depcnt[stop1];
    depofs = pdep->depofs[stop1];
    pairs = net->pairs[stop1];
    if (depofs >= pairs) {
      error(0,"net %u port %u ofs %u not in %lu",stop1,dep,depofs,pairs);
      break;
    }
    if (depofs + depcnt > pairs) {
      error(0,"net %u port %u ofs %u+%u not in %lu",stop1,dep,depofs,depcnt,pairs);
      break;
    }
    dlst = deplst + depofs;
    dlstdur = depdurlst + depofs;

    // sort mid1
    sdepcnt = 0;
    for (dmid1 = 0; dmid1 < depcnt && sdepcnt < dmid2lim; dmid1++) {
      ddmid = dlst[dmid1];
      mid1 = ddmid & Nbrmask;

      if ( (ddmid & Viabit) == 0 && (ddmid & Tripbits) != Tripbits ) continue;
      if (mid1 == arr) continue;

      pmid1 = ports + mid1;

      seq1 = pmid1->gridseq;

      dirdistm1a = xgeodist(pmid1,parr,seq1,gseqcnt,seqdist);

      if (dirdistm1a > gdistlim) continue;

      dur = dlstdur[dmid1];

      if (xview) {
        if (stop1 == 0 && dur >= curcost) continue;
        if (curcost != hi32 && dur > curcost * 2) continue;
      }
      durdist = dirdistm1a + dur * 50;

      dmid1sort[sdepcnt++] = ((ub8)durdist << 32) | dmid1;
    }
    if (sdepcnt == dmid2lim) src->mid1limcnt2++;
    if (sdepcnt > 1) fsort8(dmid1sort,sdepcnt,0,FLN,"dmid1");
    if (sdepcnt == 0) {
      info(0,"skip on none from %u mid1",depcnt);
      continue;
    }

    for (dmid1 = 0; dmid1 < sdepcnt; dmid1++) {
      x8 = dmid1sort[dmid1];
      xdmid1 = x8 & hi32;
      mid1 = dlst[xdmid1] & Nbrmask;
      dur = dlstdur[xdmid1];
      dmid1durs[dmid1] = dur;
      dmid1s[dmid1] = mid1;
    }
    dmid1cnts[stop1] = dmid1;
    org1cnts[stop1] = depcnt;
    vrb(0,"%u-stop %u from %u mid1s",stop1,dmid1,depcnt);

    hidmid1cnt = max(hidmid2cnt,dmid1);
  }
  if (hidmid1cnt == 0) return 0;

  ub4 tlim;
  ub8 t0,t1;
  ub4 limitfac = src->limitfac;

  // run all listed variations
  for (pp = pp2; pp < ppend && pp->nleg1 && pp->nleg4 == 0; pp++) {
    tlim = pp->tlim;
    if (tlim == 0 || pp->run == 0) continue;

    nleg1 = pp->nleg1;
    nleg2 = pp->nleg2;
    nleg3 = pp->nleg3;
    nleg = nleg1 + nleg2 + nleg3;
    if (nleg1 > nethileg || nleg2 > nethileg || nleg3 > nethileg) continue;

    stop1 = nleg1 - 1;
    stop2 = nleg2 - 1;
    stop3 = nleg3 - 1;

    if (stop1 >= Netn) return error(Ret0,"n-stop %u above %u",stop1,Netn);
    if (stop3 >= Netn) return error(Ret0,"n-stop %u above %u",stop3,Netn);

    fmtstring(desc,"d2 %u-%u-%u %u",nleg1,nleg2,nleg3,src->costlim);

    msgprefix(0,"%s",desc);
    if ( (net->lstlen[stop1] | net->lstlen[stop2] | net->lstlen[stop3]) == 0) continue;

    dmid1cnt = dmid1cnts[stop1];
    if (dmid1cnt == 0) continue;

    dmid2cnt = dmid2cnts[stop3];
    if (dmid2cnt == 0) continue;

    dmid1s = sdmid1s + stop1 * Dyn2_midlim;

    dmid1durs = sdmid1durs + stop1 * Dyn2_midlim;
    dmid2durs = sdmid2durs + stop3 * Dyn2_midlim;

    dmid2s = sdmid2s + stop3 * Dyn2_midlim;
    dmid2ns = sdmid2ns + stop3 * Dyn2_midlim;

    if (limitfac) {
      tlim *= limitfac;
      tx = pp->tuse * limitfac;
    } else {
      if (tlim > 1) tlim /= 2;
      tx = pp->tuse;
      if (tx > 1) tx /= 2;
    }
    tx = min(tx,txtra);
    info(0,"run %u,%u from %u,%u vias upto %u+%u/%u msec",dmid1cnt,dmid2cnt,org1cnts[stop1],org2cnts[stop3],tlim,tx,txtra);
    tlim += tx;
    txtra -= tx;

    t0 = gettime_msec();

    timelimit(src,tlim,desc,1);

    setimer(tlim,time_virtual);

    src->hisrcstop = max(src->hisrcstop,nleg - 1);

    rv = srcdyn2(net,src,pp,dep,arr,nleg1,nleg2,nleg3,
                 dmid1cnt,dmid1s,dmid1durs,
                 dmid2cnt,dmid2s,dmid2durs,dmid2ns);

    if (src->tlim == 0) {
      src->stat_tmo[2]++;
      if (pp->tuse > hiuse && pp->p0 < pp->p1) { hiuse = pp->tuse; hindx = (ub4)(pp - plan); }
    } else {
      t1 = gettime_msec();
      tx = (ub4)(t1 - t0);
      info(0,"used %u of %u ms",tx,tlim);
      txtra += tlim - min(tlim,tx);
    }

    pp->cost = src->costlim;

  } // all variants
  *ptxtra = txtra;
  *phindx = hindx;

  return rv;
} // dyn2_vars

// dynamic search using 3 vias, generic case
static int srcdyn3(lnet *net,struct srcplan *sp,search *src,ub4 dep,ub4 arr,ub4 nleg1,ub4 nleg2,ub4 nleg3,ub4 nleg4)
{
  ub4 portcnt = net->portcnt;
  ub4 thopcnt = net->thopcnt;
  ub4 *hopdist = net->hopdist;
  ub4 lodur;
  ub4 *portsbyhop = net->portsbyhop;
  ub1 txmask,mode,*modes1,*modes2,*modes3,*modes4,*mode1,*mode2,*mode3,*mode4;
  struct port *pdep,*parr,*pmid1,*pmid2,*pmid3,*ports = net->ports;
  struct chop *hops = net->chops;
  ub4 mid1,mid2,mid3,dmid1,sdmid1,dmid2,dmid3;
  ub4 dep1,dep2,dep3,dep4;
  ub8 ofs1,ofs2,ofs3,ofs4;
  ub4 n,n1,n2,n3,n4,v1,v2,v3,v4;
  ub4 rid1,rid2,rid3;
  iadrbase *conofs1,*conofs2,*conofs3,*conofs4;
  iadrbase *cnts1,*cnts2,*cnts3,*cnts4;
  block *lstblk1,*lstblk2,*lstblk3,*lstblk4;
  ub4 *conlst1,*conlst2,*conlst3,*conlst4,*lst1,*lst2,*lst3,*lst4,*lst11,*lst22,*lst33,*lst44;
  ub4 sumdt;
  ub4 evcnt;
  ub4 trip[Nleg];
  ub4 ptrip[Nleg+1];
  struct trip *stp;
  ub4 leg1,leg2,leg3,leg4,l1,l2,l3,l4;
  ub4 dist,hdist,dist1,dist2,dist3,dist4;
  ub4 walkdist1,walkdist2,walkdist3,walkdist4;
  ub4 sumwalkdist1,sumwalkdist2,sumwalkdist3,sumwalkdist4;
  ub4 nethistop = min(net->histop,src->nethistop);

  ub4 deptmin = src->deptmin;
  ub4 deptmax = src->deptmax;
  ub4 walklimit = src->walklimit;
  ub4 sumwalklimit = src->sumwalklimit;
  ub4 tdep0,tnxt;

  ub4 lodist = src->lodist;
  ub4 curcost,costlim = src->costlim;
  int havetime = 0;
  ub4 fare;
  ub4 altcnt;
  ub4 varcnt = 0;
  char sumdesc[64];
  ub4 stat_portdup = 0;
  int dbg = 0;

  if (nleg1 == 0 || nleg2 == 0 || nleg3 == 0 || nleg4 == 0) return info0(0,"skip dyn3 on no legs");

  pdep = ports + dep;
  if (pdep->valid == 0) return 0;
  parr = ports + arr;
  if (parr->valid == 0) return 0;

  error_ge(nleg1,Nstop);
  error_ge(nleg2,Nstop);
  error_ge(nleg3,Nstop);
  error_ge(nleg4,Nstop);

  ub4 nleg = nleg1 + nleg2 + nleg3 + nleg4;
  error_gt(nleg,Nstop,nleg1);

  src->de_prvhop = hi32;

  ub4 nstop1 = nleg1 - 1;
  ub4 nstop2 = nleg2 - 1;
  ub4 nstop3 = nleg3 - 1;
  ub4 nstop4 = nleg4 - 1;

  ub4 nstop = nleg - 1;
  ub4 maxleg = max(nleg1,nleg2);
  maxleg = max(maxleg,nleg3);
  maxleg = max(maxleg,nleg4);

  if (nethistop + 1 < maxleg) return info(Notty,"skip dyn3 precomputed to %u only",nethistop);

  if (net->lstlen[nstop1] == 0) return info(0,"no precomputed %u-stop net",nstop1);
  if (net->lstlen[nstop2] == 0) return info(0,"no precomputed %u-stop net",nstop2);
  if (net->lstlen[nstop3] == 0) return info(0,"no precomputed %u-stop net",nstop3);
  if (net->lstlen[nstop4] == 0) return info(0,"no precomputed %u-stop net",nstop4);

  ub4 *dlst,*deplst = net->deplst[nstop1];
  ub4 *alst,*arrlst = net->arrlst[nstop4];
  ub4 *mlst,*midlst = net->deplst[nstop2];
  ub4 *dlstdur,*depdurlst = net->depdurlst[nstop1];

  ub4 nleg12 = nleg1 + nleg2;
  ub4 nleg123 = nleg12 + nleg3;

  stp = src->trips;

  txmask = src->txmask;

  dep1 = dep2 = dep3 = hi32;

  cnts1 = net->concnt + nstop1;
  cnts2 = net->concnt + nstop2;
  cnts3 = net->concnt + nstop3;
  cnts4 = net->concnt + nstop4;

  iadrbase *cntsn1 = nethistop && net->lstlen[1] ? net->concnt + 1 : NULL;
  iadrbase *cntsn2 = nethistop > 1 && net->lstlen[2] ? net->concnt + 2 : NULL;

  if (cnts1->state == 0) return info(0,"skip dyn3 on no cnt init for %u stops",nstop1);

  if (cntsn1 && cnts1->state == 0) return info0(0,"net1 not inited");
  if (cntsn2 && cnts2->state == 0) return info0(0,"net2 not inited");

  src->hisrcstop = max(src->hisrcstop,nstop);

  fmtstring(sumdesc,"dyn3 %u+%u+%u+%u",nleg1,nleg2,nleg3,nleg4);

  lstblk1 = net->conlst + nstop1;
  conlst1 = blkdata(lstblk1,0,ub4);
  conofs1 = net->conofs + nstop1;

  lstblk2 = net->conlst + nstop2;
  conlst2 = blkdata(lstblk2,0,ub4);
  conofs2 = net->conofs + nstop2;

  lstblk3 = net->conlst + nstop3;
  conlst3 = blkdata(lstblk3,0,ub4);
  conofs3 = net->conofs + nstop3;

  lstblk4 = net->conlst + nstop4;
  conlst4 = blkdata(lstblk4,0,ub4);
  conofs4 = net->conofs + nstop4;

  modes1 = net->modes[nstop1];
  modes2 = net->modes[nstop2];
  modes3 = net->modes[nstop3];
  modes4 = net->modes[nstop4];

  error_zp(modes1,1);
  error_zp(modes2,1);
  error_zp(modes3,1);
  error_zp(modes4,1);

  ub8 x8,dmid1sort[Dyn3_mid1lim];
  ub4 dmid3s[Dyn3_midlim];
  ub4 dmid3cnts[Dyn3_midlim];
  ub4 dmid2cnt,hidmid2cnt = 0;
  ub4 dmid3cnt,dmid3lim = min(portcnt,Dyn3_midlim);
  ub4 dmid1lim = min(portcnt,Dyn3_mid1lim);

  ub8 t1,t0 = gettime_msec();

// prepare eligble mid3
  ub4 darr,ddmid,arrcnt = parr->arrcnt[nstop4];
  ub4 arrofs = parr->arrofs[nstop4];
  error_ge(arrofs + arrcnt,net->lstlen[nstop4]);
  if (arrcnt == 0) return info0(0,"skip on no mid 3 arrs");

  alst = arrlst + arrofs;

  dmid3 = 0;
  dmid3cnts[0] = 0;

  for (darr = 0; darr < arrcnt && dmid3 < dmid3lim; darr++) {
    ddmid = alst[darr];
    mid3 = ddmid & Nbrmask;

    if ( (ddmid & Viabit) == 0 && (ddmid & Tripbits) != Tripbits ) continue;
    if (mid3 == dep || mid3 == arr) continue;

    pmid3 = ports + mid3;

    n = rdiadr2(cnts4,mid3,arr);
    if (n == 0) continue;

    if (dmid3 > 3 && nleg123 == 3 && cntsn2 && rdiadr2(cntsn2,dep,mid3) == 0) continue;

    dmid3cnts[dmid3] = n;
    dmid3s[dmid3++] = mid3;
  }
  dmid3cnt = dmid3;
  if (dmid3cnt == 0) return info0(0,"skip on no mid3");
  if (dmid3cnt == dmid3lim) src->mid3limcnt3++;

  l1 = 0;

  ub4 seq1;
  ub4 gseqcnt = net->seqdlen;
  ub2 *seqdist = net->seqdist;

  ub4 depcnt = min(pdep->depcnt[nstop1],dmid1lim);
  ub4 midofs,depofs = pdep->depofs[nstop1];
  if (depofs + depcnt > net->pairs[nstop1]) {
    error(0,"net %u dep %u ofs %u above %lu",nstop1,dep,depofs + depcnt,net->pairs[nstop1]);
    return 0;
  }
  dlst = deplst + depofs;
  dlstdur = depdurlst + depofs;

  ub4 dirdistm1a,dirdist = fgeodist(pdep,parr,1);
  ub4 gdistlim = geodistlim(dirdist);
  ub4 dur,durdist;

  // prepare and sort eligible via1
  ub4 sdepcnt = 0,sdepstart = sp->p0;

  for (dmid1 = 0; dmid1 < depcnt && sdepcnt < Dyn3_mid1lim; dmid1++) {
    ddmid = dlst[dmid1];
    mid1 = ddmid & Nbrmask;

    if ( (ddmid & Viabit) == 0 && (ddmid & Tripbits) != Tripbits ) continue;
    if (mid1 == dep || mid1 == arr) continue;

    pmid1 = ports + mid1;

    seq1 = pmid1->gridseq;

    dirdistm1a = xgeodist(pmid1,parr,seq1,gseqcnt,seqdist);

    if (dirdistm1a > gdistlim) continue;

    dur = dlstdur[dmid1];
    if (nstop1 == 0 && dur >= costlim) continue;
    if (costlim != hi32 && dur > costlim * 2) continue;

    durdist = dirdistm1a + dur * 50;
    dmid1sort[sdepcnt++] = ((ub8)durdist << 32) | mid1;
  }
  if (sdepcnt > 1 && sp->sort) fsort8(dmid1sort,sdepcnt,0,FLN,"dmid1");
  if (sdepcnt == Dyn3_mid1lim) src->mid1limcnt3++;

  if (sdepstart > sdepcnt) return warn(0,"mid1 start %u above cnt %u",sdepstart,sdepcnt);
  else if (sdepstart == sdepcnt) return info(0,"mid1 start %u at end",sdepstart);

  // each mid1
  for (sdmid1 = sdepstart; sdmid1 < sdepcnt; sdmid1++) {
    x8 = dmid1sort[sdmid1];
    dirdistm1a = (ub4)(x8 >> 32);
    mid1 = x8 & hi32;
    if (mid1 == arr) continue;

    pmid1 = ports + mid1;

    if (timeout(FLN,src,sp,sdmid1,sdepcnt)) {
      info(0,"%u,x,%u vias \ah%u vars \ah%u dups",sdepcnt,dmid3cnt,varcnt,stat_portdup);
      return havetime;
    }

    n1 = rdiadr2(cnts1,dep,mid1);
    if (n1 == 0) continue;

    // each mid2
    dmid2cnt = pmid1->depcnt[nstop2];
    midofs = pmid1->depofs[nstop2];
    mlst = midlst + midofs;
    if (midofs + dmid2cnt > net->lstlen[nstop2]) {
      error(0,"net %u mid1 %u ofs %u above %lu",nstop2,mid1,midofs + dmid2cnt,net->pairs[nstop2]);
      break;
    }
    hidmid2cnt = max(hidmid2cnt,dmid2cnt);
    for (dmid2 = 0; dmid2 < dmid2cnt; dmid2++) {
      ddmid = mlst[dmid2];
      mid2 = ddmid & Nbrmask;

      if ( (ddmid & Viabit) == 0 && (ddmid & Tripbits) != Tripbits ) continue;
      if (mid2 == mid1 || mid2 == dep || mid2 == arr) continue;

      pmid2 = ports + mid2;

      if (timeout(FLN,src,sp,sdmid1,sdepcnt)) {
        info(0,"%u,%u,%u vias \ah%u vars \ah%u dups",sdepcnt,dmid2cnt,dmid3cnt,varcnt,stat_portdup);
        return havetime;
      }

      n2 = rdiadr2(cnts2,mid1,mid2);
      if (n2 == 0) continue;

      // each mid3
    sort conlst on dep and arr ?
    bsearch for larger cnt

      for (dmid3 = 0; dmid3 < dmid3cnt; dmid3++) {
        mid3 = dmid3s[dmid3];
        if (mid3 == mid1 || mid3 == mid2) continue;
        n3 = rdiadr2(cnts3,mid2,mid3);
        if (n3 == 0) continue;

#if 1
        if (timeout(FLN,src,sp,sdmid1,sdepcnt)) {
          info(0,"%u,%u,%u vias \ah%u vars \ah%u dups",sdepcnt,dmid2cnt,dmid3cnt,varcnt,stat_portdup);
          return havetime;
        }
#endif

        pmid3 = ports + mid3;

        n4 = dmid3cnts[dmid3];

        n1 = min(n1,8);
        n2 = min(n2,8);
        n3 = min(n3,8);
        n4 = min(n4,8);

        ofs1 = rdiadr8(conofs1,dep,mid1);
        ofs2 = rdiadr8(conofs2,mid1,mid2);
        ofs3 = rdiadr8(conofs3,mid2,mid3);
        ofs4 = rdiadr8(conofs4,mid3,arr);

        lst1 = conlst1 + ofs1 * nleg1;
        lst2 = conlst2 + ofs2 * nleg2;
        lst3 = conlst3 + ofs3 * nleg3;
        lst4 = conlst4 + ofs4 * nleg4;

        mode1 = modes1 + ofs1;
        mode2 = modes2 + ofs2;
        mode3 = modes3 + ofs3;
        mode4 = modes4 + ofs4;

        altcnt = 0;

        // dep-mid1
        for (v1 = 0; v1 < n1; v1++) {

          mode = mode1[v1];
          if ((mode & txmask) != mode) continue;

          lst11 = lst1 + v1 * nleg1;

          dist1 = walkdist1 = sumwalkdist1 = 0;
          lodur = 0;

          for (leg1 = 0; leg1 < nleg1; leg1++) {
            l1 = lst11[leg1];
            if (leg1) {
              dep1 = portsbyhop[l1 * 2];
              if (dep1 == arr || dep1 == mid2 || dep1 == mid3) break;
              ptrip[leg1] = dep1;
            }
            hdist = hopdist[l1];
            dist1 += hdist;
            lodur += hops[l1].lodur;
            if (l1 >= thopcnt) {
              walkdist1 += hdist;
              sumwalkdist1 += hdist;
              if (walkdist1 > walklimit) break;
            } else walkdist1 = 0;

            trip[leg1] = l1;
          }
          if (leg1 != nleg1) continue;
          if (sumwalkdist1 > sumwalklimit) continue;

          if (lodist != hi32 && dist1 > 10 * lodist) continue;
          if (lodur > costlim) continue;

          rid1 = hops[l1].rid;

          // mid1-mid2
          for (v2 = 0; v2 < n2; v2++) {

            if (altcnt > altlimit3) break;
            mode = mode2[v2];
            if ((mode & txmask) != mode) continue;

            walkdist2 = walkdist1;
            sumwalkdist2 = sumwalkdist1;

            lst22 = lst2 + v2 * nleg2;

            l2 = lst22[0];
            if (l1 >= thopcnt && l2 >= thopcnt) continue; // walk after walk

            rid2 = hops[l2].rid;
            if (pmid1->loop == 0 && rid1 != hi32 && rid1 == rid2) continue;

            dist2 = dist1;

            for (leg2 = 0; leg2 < nleg2; leg2++) {
              l2 = lst22[leg2];

              if (leg2) {
                dep2 = portsbyhop[l2 * 2];
                if (dep2 == dep || dep2 == mid3 || dep2 == arr) break;
                if (nleg1 > 1 && portintrip(dep2,ptrip+1,nleg1-1)) { stat_portdup++; break; }
              }
              hdist = hopdist[l2];
              dist2 += hdist;
              lodur += hops[l2].lodur;
              if (l2 >= thopcnt) {
                walkdist2 += hdist;
                sumwalkdist2 += hdist;
                if (walkdist2 > walklimit) break;
              } else walkdist2 = 0;

              trip[nleg1 + leg2] = l2;
              ptrip[nleg1 + leg2] = dep2;
            }
            if (leg2 != nleg2) continue;
            if (sumwalkdist2 > sumwalklimit) continue;

            if (lodist != hi32 && dist2 > 10 * lodist) continue;

            if (lodur > costlim) continue;

            // mid2-mid3
            for (v3 = 0; v3 < n3; v3++) {
              if (altcnt > altlimit3) break;
              mode = mode3[v3];
              if ((mode & txmask) != mode) continue;

              walkdist3 = walkdist2;
              sumwalkdist3 = sumwalkdist2;

              lst33 = lst3 + v3 * nleg3;

              l3 = lst33[0];
              if (l2 >= thopcnt && l3 >= thopcnt) continue;

              rid3 = hops[l3].rid;
              if (pmid2->loop == 0 && rid2 != hi32 && rid2 == rid3) continue;

              dist3 = dist2;

              for (leg3 = 0; leg3 < nleg3; leg3++) {
                l3 = lst33[leg3];

                if (leg3) {
                  dep3 = portsbyhop[l3 * 2];
                  if (dep3 == dep || dep3 == mid1 || dep3 == arr) break;
                  if (portintrip(dep3,ptrip+1,nleg1+nleg2-1)) { stat_portdup++; break; }
                }
                hdist = hopdist[l3];
                dist3 += hdist;
                if (l3 >= thopcnt) {
                  walkdist3 += hdist;
                  sumwalkdist3 += hdist;
                  if (walkdist3 > walklimit) break;
                } else walkdist3 = 0;

                trip[nleg1+nleg2+leg3] = l3;
                ptrip[nleg1+nleg2+leg3] = dep3;
              }
              if (leg3 != nleg3) continue;
              if (sumwalkdist3 > sumwalklimit) continue;

              if (lodist != hi32 && dist3 > 10 * lodist) continue;

              for (v4 = 0; v4 < n4; v4++) {
                mode = mode4[v4];
                if ((mode & txmask) != mode) continue;

                walkdist4 = walkdist3;
                sumwalkdist4 = sumwalkdist3;

                lst44 = lst4 + v4 * nleg4;

                l4 = lst44[0];
                if (l3 >= thopcnt && l4 >= thopcnt) continue;

                if (pmid3->loop == 0 && rid3 != hi32 && rid3 == hops[l4].rid) continue;

                dist4 = dist3;

                // mid3-arr
                for (leg4 = 0; leg4 < nleg4; leg4++) {
                  l4 = lst44[leg4];
                  if (leg4) {
                    dep4 = portsbyhop[l4 * 2];
                    if (dep4 == dep || dep4 == mid1 || dep4 == mid2) break;
                    if (portintrip(dep4,ptrip+1,nleg1+nleg2+nleg3-1)) { stat_portdup++; break; }
                  }
                  hdist = hopdist[l4];
                  dist4 += hdist;
                  if (l4 >= thopcnt) {
                    walkdist4 += hdist;
                    sumwalkdist4 += hdist;
                    if (walkdist4 > walklimit) break;
                  } else walkdist4 = 0;

                  trip[nleg1+nleg2+nleg3+leg4] = l4;
                }
                if (leg4 != nleg4) continue;
                if (sumwalkdist4 > sumwalklimit) continue;

                dist = dist4;
                if (dist > 1000) lodist = min(dist,lodist);
                if (havetime && lodist != hi32 && dist > 15 * lodist) continue;

                altcnt++;
                if (altcnt == altlimit3 / 2) src->stat_altlim3++;

                curcost = addevs(src,net,trip,nleg,costlim);
                if (curcost >= costlim) continue;

                t1 = gettime_msec();
                msgprefix(0,"d3 %u-%u-%u-%u %u",nleg1,nleg2,nleg3,nleg4,curcost);

                if (checktrip3(net,trip,nleg,dep,arr,mid1,hi32)) continue;
                if (checktrip3(net,trip,nleg,dep,arr,mid2,hi32)) continue;
                if (checktrip3(net,trip,nleg,dep,arr,mid3,hi32)) continue;

                infocc(dbg,0,"%u legs curcost %u costlim %u win %u",nleg,curcost,costlim,src->dephwin);

                costlim = curcost;
                havetime = 1;
                srcinfo(src,3,nleg1,nleg2,nleg3,nleg4,sdmid1,sdepcnt,t1 - t0);

#if 0
                evcnt = getevs(src,net,nleg,trip,0,"dyn3");
                if (evcnt == 0) continue;

                stp = setrip(src,net,curcost,&costlim,nleg,trip,"dyn3");
                if (stp == NULL) return 1;

                havetime = 1;
                sumdt = stp->dt;
                fare = stp->fare;

                stp->dist = dist;

                if (dist < src->lodist) src->lodist = dist;
                src->costlim = costlim;

                src->timestop = min(src->timestop,nstop);

                tdep0 = src->curts[0];
                evcnt = getevs(src,net,nleg,trip,1,"dyn3");
                if (evcnt) tnxt = max(src->curts[0],tdep0) - tdep0;
                else tnxt = hi32;

                t1 = gettime_msec();
                fmtstring(sumdesc,"dyn3 %u+%u+%u+%u/%s at %lu ms",nleg1,nleg2,nleg3,nleg4,src->dwinfo,t1 - t0);
                fmtsum(FLN,stp,sumdt,tnxt,dist4,fare,curcost,sumdesc);
#endif
                info(0,"found \av%u%p win %u t %lu",nleg,(void *)trip,src->dephwin,t1 - t0);

              } // each v4
            } // each v3
          } // each v2
        } // each v1

//        infocc(altcnt == altlimit3 / 2,Notty,"%u of max %u alts",altcnt,altlimit3)

        varcnt += altcnt;
      } // each mid3
    } // each mid2
  } // each mid1

  info(0,"%u,%u,%u vias \ah%u vars \ah%u dups",sdepcnt,hidmid2cnt,dmid3cnt,varcnt,stat_portdup);

  if (havetime) return 1;

  info(V0,"no time for %u-stop trip %u-%u on \ad%u-\ad%u",nleg-1,dep,arr,deptmin,deptmax);
  src->lodist = lodist;

  return 0;
} // dyn3 n-leg

dyn4 ?

// infinite transfer search
static int srcinf(lnet *net,search *src,ub4 dep,ub4 arr,ub4 nstophi)
{
  ub4 prvcnt,concnt = 0;
  ub4 iter = 0,iterhi = 0;
  ub4 arr1,dep1,darr1,tdep1,ddarr,cdep,carr;
  ub4 leg,nleg,stop,l;
  ub4 dist,fare,cnt,evcnt;
  ub4 portcnt = net->portcnt;
  iadrbase *cnts = net->concnt;
  iadrbase *ofss = net->conofs;
  struct port *pdep,*pdep1,*ports = net->ports;
  ub4 *hopdist = net->hopdist;
  ub4 *portsbyhop = net->portsbyhop;
  ub4 trip[Nleg];
  struct trip *stp;
  ub1 txmask = src->txmask;
  ub1 *modes = net->hopmodes;

  ub4 curcost,costlim = src->costlim;
  int havetime = (src->trips[0].len != 0);
  ub8 ofs;
  ub4 *lst,*lstv;
  block *lstblk = net->conlst;

  lst = blkdata(lstblk,0,ub4);

  ub1 *conns = src->infconns;
  ub4 *dconns,*tconns,*aconns,*daconns = src->infdaconns;

  nsethi(daconns,portcnt);
  nclear(conns,portcnt);

  int dbg = 0;

  ub8 t1,t0 = gettime_msec();

  ub4 tdep0,tnxt,sumdt;
  char sumdesc[64];

  src->de_prvhop = hi32;

  ub4 *dlst,*deplst = net->deplst[0];

  pdep = ports + dep;

  ub4 depcnt = pdep->depcnt[0];
  ub4 depofs = pdep->depofs[0];

  dlst = deplst + depofs;

  // direct links
  aconns = daconns;
  for (darr1 = 0; darr1 < depcnt; darr1++) {
    ddarr = dlst[darr1];
    arr1 = ddarr & Nbrmask;
    if (dep == arr1) continue;
    if (arr1 == arr) {
      info(0,"found %u-%u at 1 leg",dep,arr);
      // todo store
    }
    conns[arr1] = 1;
    aconns[arr1] = dep; concnt++;
  }

  do {
    prvcnt = concnt;
    dconns = daconns + portcnt * iter;

    iter++;
    if (iter >= Nstop) break;

    iterhi = max(iterhi,iter);
    aconns = daconns + portcnt * iter;
    nsethi(aconns,portcnt);

    // subsequent indirect links
    for (dep1 = 0; dep1 < portcnt; dep1++) {
      if (dconns[dep1] == hi32) continue;

      pdep1 = ports + dep1;
      depcnt = pdep1->depcnt[0];
      depofs = pdep1->depofs[0];
      dlst = deplst + depofs;

      for (darr1 = 0; darr1 < depcnt; darr1++) {
        ddarr = dlst[darr1];
        arr1 = ddarr & Nbrmask;
        error_ge(arr1,portcnt);
        if (dep == arr1) continue;

        if (arr1 == arr) { // reached complete trip. do not mark to continue alternatives
          concnt++;
          nleg = iter + 1;
          // info(0,"found %u-%u at %u legs dep1 %u darr %u",dep,arr,nleg,dep1,darr1);

          // reconstruct trip
          dist = 0;
          l = iter;
          tconns = dconns;
          tdep1 = dep1;
          do {
            cnt = rdiadr2(cnts,tdep1,arr1);
            if (cnt == 0) return error(Ret0,"leg %u invalid hop %u-%u",iter,tdep1,arr1);
            ofs = rdiadr8(ofss,tdep1,arr1);
            lstv = lst + ofs;
            leg = lstv[0];
            cdep = portsbyhop[leg * 2];
            carr = portsbyhop[leg * 2 + 1];
            if (l < iter && carr == arr) {
              warn(0,"leg %u/%u arr equals final arr %u",l,iter,arr);
              break;
            }
            if (l && cdep == dep) {
              warn(0,"leg %u/%u dep equals initial dep %u",l,iter,dep);
              break;
            }
            if ( (modes[leg] & txmask) == 0) break;
            info(V0,"leg %u hop %u dep %u arr %u",iter,leg,tdep1,arr1);
            trip[l] = leg;
            l--;
            dist += hopdist[leg];
            arr1 = tdep1;
            error_ge_cc(tconns[tdep1],portcnt,"leg %u iter %u dep1 %u",l,iter,tdep1);
            tdep1 = tconns[tdep1];
            tconns -= portcnt;
            if (tdep1 == hi32) return error(Ret0,"iter %u arr1 %u invalid",iter,arr1);
          } while (l);
          if (l) continue;
          cnt = rdiadr2(cnts,dep,arr1);
          if (cnt == 0) return error(Ret0,"leg %u invalid hop %u-%u",l,dep,arr1);
          ofs = rdiadr8(ofss,dep,arr1);
          lstv = lst + ofs;
          leg = lstv[0];
          carr = portsbyhop[leg * 2 + 1];
          if (carr == arr) {
            warn(0,"leg %u/%u arr equals final arr %u",l,iter,arr);
            continue;
          }
          // info(V0,"leg %u hop %u dep %u arr %u",l,leg,dep,arr1);
          dist += hopdist[leg];
          trip[l] = leg;

          if (dep == trip[nleg-1]) {
            warn(0,"final leg %u arr equals dep %u",nleg-1,dep);
            continue;
          }
          if (checktrip(net,trip,nleg,dep,arr,hi32)) return 0;

          curcost = addevs(src,net,trip,nleg,costlim);

          if (curcost >= costlim) {
            vrb0(0,"%u legs cost %u win %u",nleg,curcost,src->dephwin);
            continue;
          }

          evcnt = getevs(src,net,nleg,trip,0,"inf");
          if (evcnt == 0) return info(0,"no evs for costlim %u",costlim);
          msgprefix(0,"inf %u",costlim);

          havetime = 1;
          info(0,"%u-%u at %u legs dep1 %u darr %u",dep,arr,nleg,dep1,darr1);
          info(0,"found \av%u%p %u event\as cost %u win %u",nleg,(void *)trip,evcnt,curcost,src->dephwin);
          stop = nleg - 1;

#if 0
          stp = setrip(src,net,curcost,&costlim,nleg,trip,"inf");
          if (stp == NULL) return 1;

          sumdt = stp->dt;
          fare = stp->fare;
          stp->dist = dist;

          if (dist < src->lodist) src->lodist = dist;
          src->costlim = costlim;

          tdep0 = src->curts[0];
          evcnt = getevs(src,net,nleg,trip,1,"inf");
          if (evcnt) tnxt = max(src->curts[0],tdep0) - tdep0;
          else tnxt = hi32;
          t1 = gettime_msec();
          fmtstring(sumdesc,"srcinf %u/%s at %lu ms",concnt,src->dwinfo,t1 - t0);
          fmtsum(FLN,stp,sumdt,tnxt,dist,fare,curcost,sumdesc);
          src->timestop = min(src->timestop,stop);
#endif

        } else if ( (ddarr & Viabit) && conns[arr1] == 0) { // no complete trip
          conns[arr1] = 1; concnt++;
          error_ge(dep1,portcnt);
          aconns[arr1] = dep1;
        } else { // optionally replace ?
        }
      }
      if (timeout(FLN,src,NULL,iter,nstophi)) return havetime;

    }
    info(0,"iter %u conns %u",iter,concnt);
  } while (concnt > prvcnt && iter < nstophi);
  info(0,"end at iter %u",iter);
  return havetime;
}

// assign time limits for complete search
// scaled by: lowest = 1 low = 2 medium = 4 high = 8 highest = 16
// aim at medium sum = 1 sec 600 ms @ 8 items 80

static struct csrcplan cplan3[] = { // 3-stop precomputed

 // dyn0 net 0..2
 { 1,0,0,0, 5,2,1 }, // 0
 { 2,0,0,0, 5,2,1 }, // 5
 { 3,0,0,0, 8,2,1 }, // 15
 { 4,0,0,0, 5,2,1 }, // 2

 // dyn1
 { 1,1,0,0, 3,1,1 }, // 0
 { 2,1,0,0, 4,1,1 }, //3 3
 { 1,2,0,0, 4,1,1 }, //3 0
 { 2,2,0,0, 15,5,1 }, //4 31
 { 3,1,0,0, 5,5,1 }, //4
 { 1,3,0,0, 5,5,1 }, //4
 { 3,2,0,0, 12,8,1 }, //5 19
 { 2,3,0,0, 10,5,1 }, //5 15
 { 3,3,0,0, 18,10,1 }, //6 23
 { 2,4,0,0, 5,2,1 }, //6
 { 4,3,0,0, 7,2,1 }, //7 8
 { 3,4,0,0, 6,3,1 }, //8 5
 { 4,4,0,0, 5,3,1 }, //9 0

 // dyn2
 { 1,1,1,0, 0,1,1 }, //3  0 0

 { 1,1,2,0, 2,2,1 }, //4  3 0
 { 1,2,1,0, 2,2,1 }, //4  3 0
 { 2,1,1,0, 2,2,1 }, //4  3 0

 { 1,1,3,0, 2,3,1 }, //5  7 1
 { 1,2,2,0, 6,5,1 }, //5 26  4
 { 1,3,1,0, 4,4,1 }, //5  12 1
 { 2,1,2,0, 4,4,1 }, //5 10 2
 { 2,2,1,0, 2,2,1 }, //5  2 0
 { 3,1,1,0, 2,2,1 }, //5  2 0

 { 1,2,3,0, 12,10,1 }, //6   54 13
 { 1,3,2,0, 20,15,1 }, //6   84 23
 { 2,1,3,0, 2,5,1 }, //6   25 4
 { 2,2,2,0, 6,5,1 }, //6   55 8
 { 2,3,1,0, 2,6,1 }, //6   10 0
 { 3,1,2,0, 2,6,1 }, //6   14 1
 { 3,2,1,0, 2,6,1 }, //6   4 1

 { 1,3,3,0, 25,25,1 }, //7  164 39
 { 2,2,3,0, 20,20,1 }, //7  112 24
 { 2,3,2,0, 15,15,1 }, //7  89 13
 { 3,1,3,0, 8,8,1 }, //7  40 8
 { 3,2,2,0, 6,8,1 }, //7   42 4
 { 3,3,1,0, 5,8,1 }, //7  13 2

 { 2,3,3,0, 30,30,1 }, //8  207 53
 { 3,2,3,0, 15,20,1 }, //8   84 19
 { 3,3,2,0, 10,10,1 }, //8    67 9

 { 3,3,3,0, 25,25,1 }, //9   166 41

 { 4,3,3,0, 5,10,1 }, //10   6 2
 { 4,4,3,0, 5,10,1 }, //11   8 1
 { 4,4,4,0, 5,10,1 }, //12  1 0

 // dyn3
 { 2,1,1,1, 0,0,0 }, //5 0
 { 2,2,1,1, 1,5,0 }, //6 2
 { 2,2,2,1, 3,10,1 }, //7 5
 { 2,2,2,2, 15,15,1 }, //8 21
 { 3,2,2,2, 15,15,1 }, //9 17

 { 3,3,2,2, 15,15,1 }, //10 18
 { 2,2,3,3, 10,10,1 }, //10 7
 { 2,3,3,3, 12,15,1 }, //11 12
 { 3,3,3,2, 10,10,1 }, //11 6
 { 3,3,3,3, 8,10,1 }, //12 2

 { 3,3,3,4, 3,5,1 }, //13
 { 4,3,3,3, 3,5,1 }, //13 1
 { 4,4,3,3, 3,5,1 }, //14 1
 { 4,4,4,3, 3,5,1 }, //15
 { 4,4,4,4, 3,5,1 }, //16

 { 0,0,0,0, 15,200,0 } // inf
};

static struct csrcplan cplan2[] = { // 2-stop precomputed

 // dyn0 net 0..2
 { 1,0,0,0, 5,2,1 }, // 0
 { 2,0,0,0, 5,2,1 }, // 5
 { 3,0,0,0, 8,2,1 }, // 15

 // dyn1
 { 1,1,0,0, 3,1,1 }, // 0
 { 2,1,0,0, 4,1,1 }, //3 3
 { 1,2,0,0, 4,1,1 }, //3 0
 { 2,2,0,0, 15,5,1 }, //4 31
 { 3,2,0,0, 10,5,1 }, //5 19
 { 2,3,0,0, 10,5,1 }, //5 15
 { 3,3,0,0, 15,5,1 }, //6 23

 // dyn2
 { 1,1,1,0, 0,1,1 }, //3  0 0

 { 1,1,2,0, 2,2,1 }, //4  3 0
 { 1,2,1,0, 2,2,1 }, //4  3 0
 { 2,1,1,0, 2,2,1 }, //4  3 0

 { 1,1,3,0, 2,3,1 }, //5  7 1
 { 1,2,2,0, 6,5,1 }, //5 26  4
 { 1,3,1,0, 4,4,1 }, //5  12 1
 { 2,1,2,0, 4,4,1 }, //5 10 2
 { 2,2,1,0, 2,2,1 }, //5  2 0
 { 3,1,1,0, 2,2,1 }, //5  2 0

 { 1,2,3,0, 12,10,1 }, //6   54 13
 { 1,3,2,0, 20,15,1 }, //6   84 23
 { 2,1,3,0, 2,5,1 }, //6   25 4
 { 2,2,2,0, 6,5,1 }, //6   55 8
 { 2,3,1,0, 2,6,1 }, //6   10 0
 { 3,1,2,0, 2,6,1 }, //6   14 1
 { 3,2,1,0, 2,6,1 }, //6   4 1

 { 1,3,3,0, 25,25,1 }, //7  164 39
 { 2,2,3,0, 20,20,1 }, //7  112 24
 { 2,3,2,0, 15,15,1 }, //7  89 13
 { 3,1,3,0, 8,8,1 }, //7  40 8
 { 3,2,2,0, 6,8,1 }, //7   42 4
 { 3,3,1,0, 5,8,1 }, //7  13 2

 { 2,3,3,0, 30,30,1 }, //8  207 53
 { 3,2,3,0, 15,20,1 }, //8   84 19
 { 3,3,2,0, 10,10,1 }, //8    67 9

 { 3,3,3,0, 25,25,1 }, //9   166 41

 // dyn3
 { 2,1,1,1, 0,0,0 }, //5 0
 { 2,2,1,1, 1,5,0 }, //6 2
 { 2,2,2,1, 3,10,1 }, //7 5
 { 2,2,2,2, 15,10,1 }, //8 21
 { 3,2,2,2, 15,10,1 }, //9 17

 { 3,3,2,2, 20,15,1 }, //10 18 .
 { 2,2,3,3, 10,10,1 }, //10 7
 { 2,3,3,3, 25,25,1 }, //11 12 .
 { 3,3,3,2, 15,15,1 }, //11 6 .
 { 3,3,3,3, 15,15,1 }, //12 2

 { 0,0,0,0, 15,200,0 } // inf
};

static struct csrcplan cplan1[] = { // 1-stop precomputed

 // dyn0 net 0..2
 { 1,0,0,0, 5,1,1 },
 { 2,0,0,0, 10,2,1 },

 // dyn1
 { 1,1,0,0, 5,5,1 }, //2
 { 2,1,0,0, 15,15,1 }, //3
 { 1,2,0,0, 5,5,1 }, //3
 { 2,2,0,0, 25,25,1 }, //4

 // dyn2
 { 1,1,1,0, 2,2,1 }, //3

 { 1,1,2,0, 5,5,1 }, //4
 { 1,2,1,0, 15,15,1 }, //4
 { 2,1,1,0, 5,5,1 }, //4

 { 1,2,2,0, 35,35,1 }, //5
 { 2,1,2,0, 25,25,1 }, //5
 { 2,2,1,0, 15,15,1 }, //5

 { 2,2,2,0, 45,40,1 }, //6

 // dyn3
 { 1,1,1,1, 1,2,0 }, //4
 { 1,1,2,2, 15,10,1 }, //6

 { 2,2,2,1, 40,40,1 }, //7
 { 2,2,2,2, 20,20,1 }, //8

 { 0,0,0,0, 100,200,0 } // inf
};

static struct csrcplan cplan0[] = { // 0-stop precomputed

 // dyn0 net 0..2
 { 1,0,0,0, 10,5,1 },

 // dyn1
 { 1,1,0,0, 20,20,1 }, //2

 // dyn2
 { 1,1,1,0, 20,30,1 }, //3

 // dyn3
 { 1,1,1,1, 80,80,1 }, //4

 { 0,0,0,0, 400,400,0 } // inf
};

static ub4 inftimes[Netn];
static ub4 infnotimes[Netn];

static void showplan(ub4 histop)
{
  ub4 tlim,tuse,tsum;
  ub4 planstop,nleg1,nleg2,nleg3,nleg4,nleg;
  ub4 dyn,prvdyn = hi32;
  ub4 planlen = 0;
  struct srcplan *sp,*plan;

  switch (histop) {
    case 0: plan = plan0; planstop = 0; break;
    case 1: plan = plan1; planstop = 1; break;
    case 2: plan = plan2; planstop = 2; break;
    case 3: plan = plan3; planstop = 3; break;
    default: plan = plan3; planstop = 3;
  }

  info(0,"%u-stop plan in effect for %u stops",planstop,histop);

  info(User,"\nstatic struct csrcplan cplan%u[] = {\n",histop);

  sp = plan;
  tsum = 0;
  while (sp->nleg1) {

    nleg1 = sp->nleg1;
    nleg2 = sp->nleg2;
    nleg3 = sp->nleg3;
    nleg4 = sp->nleg4;

    nleg = nleg1 + nleg2 + nleg3 + nleg4;

    tlim = sp->tlim;
    tuse = sp->tuse;

    if (nleg2 == 0) dyn = 0;
    else if (nleg3 == 0) dyn = 1;
    else if (nleg4 == 0) dyn = 2;
    else dyn = 3;

    if (dyn != prvdyn) info(User,"\n  // dyn%u",dyn);
    prvdyn = dyn;

    tsum += sp->tlim;
    info(User,"  { %u,%u,%u,%u, %2u,%2u,1 }, // %u leg\as  %u sum",
      nleg1,nleg2,nleg3,nleg4,tlim,tuse,nleg,tsum);
    sp++;
    planlen++;
    if (planlen >= Planlen) {
      warn(0,"unterminated plan %u",histop);
      break;
    }
  }
  info0(User,"\n  // srcinf when read from file");
  info(User," { 0,0,0,0  %u,%u,1 }",inftimes[histop],infnotimes[histop]);
  info0(User,"};\n");
  info(User,"static ub4 inftime = %u; // static config",inftimes[histop]);
  info(User,"static ub4 infnotime = %u;\n",infnotimes[histop]);
}

static int loadcplan(ub4 histop,ub4 show)
{
  struct srcplan *sp,*plan;
  struct csrcplan *csp,*cplan;
  ub4 planlen = 0;
  ub4 tlim,tuse;
  ub4 nleg1,nleg2,nleg3,nleg4,hileg;

  error_ge(histop,Nstop);
  error_ge(histop,Netn);
  hileg = histop + 1;

  switch (histop) {
  case 0: plan = plan0; cplan = cplan0; break;
  case 1: plan = plan1; cplan = cplan1; break;
  case 2: plan = plan2; cplan = cplan2; break;
  case 3: plan = plan3; cplan = cplan3; break;
  default: return error(0,"unsupported plan %u",histop);
  }

  info(V1,"loading static %u-stop plan",histop);

  csp = cplan;
  sp = plan;
  int dif = 0;

  while (csp->nleg1) {
    nleg1 = csp->nleg1;
    nleg2 = csp->nleg2;
    nleg3 = csp->nleg3;
    nleg4 = csp->nleg4;

    error_gt(nleg1,hileg,planlen);
    error_gt(nleg2,hileg,planlen);
    error_gt(nleg3,hileg,planlen);
    error_gt(nleg4,hileg,planlen);

    sp->ndx = planlen;
    dif = (sp->nleg1 != nleg1) | (sp->nleg2 != nleg2) | (sp->nleg3 != nleg3) | (sp->nleg4 != nleg4);

    sp->nleg1 = nleg1;
    sp->nleg2 = nleg2;
    sp->nleg3 = nleg3;
    sp->nleg4 = nleg4;

    tlim = csp->tlim;
    tuse = csp->tlim;
    error_ge(tlim,2000);
    error_ge(tuse,2000);

    dif |= (sp->tlim != tlim) | (sp->tuse != tuse);
    sp->tlim = tlim;
    sp->tuse = tuse;
    csp++;
    sp++;
    planlen++;
    error_ge(planlen + 1,Planlen);
  }
  dif |= (sp->nleg1 != 0);
  sp->nleg1 = 0;

  tlim = csp->tlim;
  tuse = csp->tlim;
  error_ge(tlim,2000);
  error_ge(tuse,2000);

  inftimes[histop] = tlim;
  infnotimes[histop] = tuse;

  if (dif) {
    if (show) showplan(histop);
  } else info(V0,"no dif for %u items",planlen);

  return 0;
}

static int loadplan(ub4 histop,ub4 show)
{
  struct srcplan *sp,*plan;
  ub4 planlen = 0;
  struct myfile mf;
  int fd;
  char name[256];
static ub8 prvmtimes[8];
  ub8 mtime;
  char c,buf[4096];
  ub4 len,maxlen = sizeof(buf);
  sb8 nr;

  error_ge(histop,Nstop);

  oclear(mf);

  fmtstring(name,"%s-%u.cfg",plancfgname,histop);
  fd = osopen(name);
  if (fd == -1) return info(Ret1|V1,"no %s",name); // tmp debug

  vrb0(0,"loading plan %s",name);

  if (osfdinfo(&mf,fd)) { osclose(fd); return oserror(0,"cannot stat %s",name); }

  if (mf.len < 10) { osclose(fd); return error(0,"%s is empty (%lu)",name,mf.len); }
  else if (mf.len > maxlen) { osclose(fd); return error(0,"%s exceeds %u",name,maxlen); }

  len = (ub4)mf.len;

  mtime = mf.mtime;
  if (mtime <= prvmtimes[histop]) {
    osclose(fd);
    return info(V0,"%s at %lu not newer than previous %lu",name,mtime,prvmtimes[histop]);
  }

  info(0,"loading plan %s",name);

  ub4 now = gettime_sec();
  if (mtime >= now || now - mtime < 2) { // safeguard for reading in-flight file
    osclose(fd);
    return info(0,"%s at %lu considered in-flight around now %u",name,mtime,now);
  }

  char timestr[64];
  sec70toyymmdd((ub4)mtime,12,timestr,sizeof(timestr)-1);
  info(0,"new %u-stop plan at time %s",histop,timestr);

  prvmtimes[histop] = mtime;

  nr = osread(fd,buf,len);
  if (nr == -1) { osclose(fd); return oserror(0,"cannot read %s",name); }
  osclose(fd);
  if (nr != len) return error(0,"partial read %ld/%u of %s",nr,len,name);

  ub4 hileg = histop + 1;

  switch (histop) {
  case 0: plan = plan0; break;
  case 1: plan = plan1; break;
  case 2: plan = plan2; break;
  case 3: plan = plan3; break;
  default: return error(0,"unsupported plan %u",histop);
  }

  ub4 leg1 = 0,leg2 = 0,leg3 = 0,leg4 = 0,tlim = 0,tuse = 0;
  enum states { Out,Fls,Leg1,Leg2,Leg3,Leg4,Tlim,Tuse,Eof };
  sp = plan;
  enum states state = Out;
  ub4 pos = 0;
  ub4 linno = 1,colno = 0;
  int dif = 0;

  while (pos < len && state != Eof) {

  c = buf[pos++];
  colno++;

  switch(state) {
  case Out:
    if (c == '/') state = Fls;
    else if (c == '{') {
      state = Leg1;
      leg1 = leg2 = leg3 = leg4 = tlim = tuse = 0;
    }
    break;

  case Leg1: if (c >= '0' && c <= '9') leg1 = leg1 * 10 + c - '0';
             else if (c == ',') state = Leg2;
             else if (c != ' ') return error(0,"line %u: unexpected char %c",linno,c);
             break;
  case Leg2: if (c >= '0' && c <= '9') leg2 = leg2 * 10 + c - '0';
             else if (c == ',') state = Leg3;
             else if (c != ' ') return error(0,"line %u: unexpected char %c",linno,c);
             break;
  case Leg3: if (c >= '0' && c <= '9') leg3 = leg3 * 10 + c - '0';
             else if (c == ',') state = Leg4;
             else if (c != ' ') return error(0,"line %u: unexpected char %c",linno,c);
             break;
  case Leg4: if (c >= '0' && c <= '9') leg4 = leg4 * 10 + c - '0';
             else if (c == ',') state = Tlim;
             else if (c != ' ') return error(0,"line %u: unexpected char %c",linno,c);
             break;

  case Tlim: if (c >= '0' && c <= '9') tlim = tlim * 10 + c - '0';
             else if (c == ',') state = Tuse;
             else if (c != ' ') return error(0,"line %u: unexpected char %c",linno,c);
             break;

  case Tuse: if (c >= '0' && c <= '9') tuse = tuse * 10 + c - '0';
             else if (c == ',') {
               if (leg1 > hileg) return error(0,"line %u: leg %u above net %u",linno,leg1,hileg);
               if (leg2 > hileg) return error(0,"line %u: leg %u above net %u",linno,leg2,hileg);
               if (leg3 > hileg) return error(0,"line %u: leg %u above net %u",linno,leg3,hileg);
               if (leg4 > hileg) return error(0,"line %u: leg %u above net %u",linno,leg4,hileg);
               if (sp->nleg1 != leg1 || sp->nleg2 != leg2 || sp->nleg3 != leg3 || sp->nleg4 != leg4) dif = 1;
               if (sp->tlim != tlim || sp->tuse != tuse) dif = 1;
               sp->nleg1 = leg1;
               sp->nleg2 = leg2;
               sp->nleg3 = leg3;
               sp->nleg4 = leg4;
               sp->tlim = tlim;
               sp->tuse = tuse;
               vrb0(0,"item %u %u,%u,%u,%u dif %d",planlen,leg1,leg2,leg3,leg4,dif);
               vrb0(0,"org  %u %u,%u,%u,%u",planlen,sp->nleg1,sp->nleg2,sp->nleg3,sp->nleg4);
               sp++;
               planlen++;
               if (planlen + 1 >= Planlen) return error(0,"line %u: plan %u exceeds len %u",linno,histop,planlen);
               if (leg1 == 0) { // srcinf
                 state = Eof;
                 if (inftimes[histop] != tlim || infnotimes[histop] != tuse) dif = 1;
                 inftimes[histop] = tlim;
                 infnotimes[histop] = tuse;
               } else state = Fls;
             } else if (c != ' ') return error(0,"line %u.%u state %u: unexpected char %c",linno,colno,state,c);
             break;

  case Fls: if (c == '\n') state = Out; break;
  case Eof: break;
  }
  if (c == '\n') { linno++; colno = 0; }
  }

  if (sp->nleg1) dif = 1;
  sp->nleg1 = 0;

  if (dif) {
    if (show) showplan(histop);
  } else info(V0,"no dif for %u items",planlen);

  return 0;
}

int loadplans(void)
{
  ub4 histop;
  sassert(Netn < 5,"Unsupported Netn");

  ub4 show = dyncfg("search.showplan",0,1);

  for (histop = 0; histop < Netn; histop++) {
    if (loadplan(histop,show)) {
      if (loadcplan(histop,show)) return 1;
    }
  }
  return 0;
}

// toplevel: proceed over transfer count, dynamic seach and precomputed nets
static int dosrc(struct network *net,ub4 nstoplo,ub4 nstophi,search *src,char *ref)
{
  ub4 gportcnt = net->portcnt;
  ub4 dep = src->dep;
  ub4 arr = src->arr;
  ub4 dyn,tlim,tsum = 0,txtra = 0,tx;
  ub4 limitfac = src->limitfac;
  ub4 nstop,nleg,nethistop;
  struct port *pdep,*parr,*ports;

  int rv = 1;

  if (gportcnt == 0) return error(0,"search without ports, ref %s",ref);

  ports = net->ports;
  nethistop = min(net->histop,src->nethistop);
  ub4 nethileg = nethistop + 1;

  ub4 portcnt = net->portcnt;
  error_z(portcnt,0);

  error_ge(dep,portcnt);
  error_ge(arr,portcnt);

  pdep = ports + dep;
  parr = ports + arr;

  if (pdep->valid == 0) return info(0,"dep %u not valid %s",dep,pdep->iname);
  if (parr->valid == 0) return info(0,"arr %u not valid %s",arr,parr->iname);

  ub4 costndx;
  ub4 cost,cost20;
  ub4 hindx2 = hi32;

  ub4 seqdep = pdep->gridseq;
  ub4 seqarr = parr->gridseq;

  ub4 gseqcnt = net->seqdlen;
  ub1 lotx,*seqlotx = net->seqlotx;

  if (seqlotx) {
    lotx = seqlotx[(ub8)seqdep * gseqcnt + seqarr];
    info(0,"lotx %u for %u,%u %s to %s",lotx,seqdep,seqarr,pdep->iname,parr->iname);
  } else {
    lotx = 0;
    info(V0,"no lotx for %u,%u %s to %s",seqdep,seqarr,pdep->iname,parr->iname);
  }

  struct srcplan *sp,*pp,*hisp,*plan;
  struct srcplan xplan[2]; // single run for leftover time dyn2
  ub4 planlen = 0;

  aclear(xplan);

  switch (nethistop) {
  case 0: plan = plan0; break;
  case 1: plan = plan1; break;
  case 2: plan = plan2; break;
  case 3: plan = plan3; break;
  default: plan = plan3;
  }
  error_z(plan->nleg1,nethistop);

  ub4 nleg1,nleg2,nleg3,nleg4;
  char desc[128];
  char costbuf[128];
  ub8 t0,t1;

  ub4 hiuse = 0;

  ub4 distlim,dist = src->geodist;

  // skip tranfers below minimum needed
  pp = sp = hisp = plan;
  txtra = 0;
  while (sp->nleg1) {
    planlen++;
    if (planlen >= Planlen) {
      warn(0,"plan %u unterminated",nethistop);
      sp->nleg1 = 0;
      break;
    }
    sp->run = 0;
    sp->p0 = 0;
    sp->p1 = 0;
    sp->cost = hi32;
    tlim = sp->tlim;
    tsum += tlim;
    nleg = sp->nleg1 + sp->nleg2 + sp->nleg3 + sp->nleg4;
    if (lotx != 0xff && nleg - 1 < lotx) {
      info(0,"skip %u-stop on min tx %u",nleg - 1,lotx);
      txtra += tlim;
      sp++;
      continue;
    }

    // skip high #transfers for small distances
    switch (nleg) {
    case 1: case 2: distlim = 0; break;
    case 3: distlim = 200; break;
    case 4: distlim = 400; break;
    case 5: distlim = 900; break;
    case 6: distlim = 2000; break;
    case 7: distlim = 3000; break;
    case 8: distlim = 4000; break;
    case 9: distlim = 6000; break;
    case 10: distlim = 8000; break;
    case 11: distlim = 9000; break;
    case 12: distlim = 20000; break;
    case 13: distlim = 30000; break;
    case 14: distlim = 40000; break;
    case 15: distlim = 50000; break;
    default: distlim = 60000; break;
    }
    if (dist < distlim) {
      info(0,"skip %u-leg on dist \ag%u < %u",nleg,dist,distlim);
      txtra += tlim;
    } else {
      info(0,"run %u-leg on dist \ag%u >= %u",nleg,dist,distlim);
      sp->run = 1;
    }
    sp++;
  }

  infocc(src->cmdseq < 2,0,"plan total base time %u msec",tsum);

  sp = pp;

  while (sp->nleg1) {
    if (sp->run == 0) { sp++; continue; }
    nleg1 = sp->nleg1;
    nleg2 = sp->nleg2;
    nleg3 = sp->nleg3;
    nleg4 = sp->nleg4;

    nleg = nleg1 + nleg2 + nleg3 + nleg4;

    tlim = sp->tlim;

    if (nleg2 == 0) dyn = 0;
    else if (nleg3 == 0) dyn = 1;
    else if (nleg4 == 0) dyn = 2;
    else dyn = 3;

    fmtstring(desc,"dyn%u %u-%u-%u-%u",dyn,nleg1,nleg2,nleg3,nleg4);
    if (nleg1 > nethileg || nleg2 > nethileg || nleg3 > nethileg || nleg4 > nethileg) {
      info(0,"skip %s on no precomputed net %u",desc,nethistop+1);
      sp++;
      continue;
    }

    nstop = nleg - 1;
    if (nstop < nstoplo) { info(0,"skip %s on %u stops below %u",desc,nstop,nstoplo); sp++; continue; }
    if (nstop > nstophi) { info(0,"skip %s on %u stops above %u",desc,nstop,nstophi); sp++; continue; }

    cost = src->costlim;
    if (dyn != 2) {

      if (limitfac) {
        tlim *= limitfac;
        tx = pp->tuse * limitfac;
      } else {
        if (tlim > 1) tlim /= 2;
        tx = pp->tuse;
        if (tx > 1) tx /= 2;
      }

      if (cost != hi32) myutoa(costbuf,cost);
      else { costbuf[0] = '-'; costbuf[1] = 0; }
      switch(dyn) {
        case 0: msgprefix(0,"d0 %u-x-x %s",nleg1,costbuf); break;
        case 1: msgprefix(0,"d1 %u-%u-x %s",nleg1,nleg2,costbuf); break;
        case 3:
        default: msgprefix(0,"d3 %u-%u-%u-%u %s",nleg1,nleg2,nleg3,nleg4,costbuf);
      }
      tx = min(tx,txtra);
      info(0,"run upto %u+%u/%u msec",tlim,tx,txtra); // todo check
      tlim += tx;
      txtra -= tx;
      timelimit(src,tlim,desc,1);

      setimer(tlim,time_virtual);
    }
    t0 = gettime_msec();

    costndx = (ub4)(sp - plan);

    switch (dyn) {
    case 0: rv = srcdyn0(net,src,dep,arr,nleg1); break;
    case 1: rv = srcdyn1(net,sp,src,dep,arr,nleg1,nleg2); break;
    case 2: rv = srcdyn2_var(net,src,dep,arr,plan,costndx,&txtra,&hindx2);
            msgprefix(0,NULL);
            while (sp->nleg3 && sp->nleg4 == 0) sp++;  // skip to first dyn3
            break;

    case 3: rv = srcdyn3(net,sp,src,dep,arr,nleg1,nleg2,nleg3,nleg4); break;
    default: return 1;
    }

    if (dyn != 2) sp->cost = src->costlim;

    if (src->tlim == 0) {
      src->stat_tmo[dyn]++;
      if (sp->tuse > hiuse && sp->p0 < sp->p1) { hiuse = sp->tuse; hisp = sp; }
      sp++;
    } else if (dyn != 2) {  // rollover unused time
      t1 = gettime_msec();
      tx = (ub4)(t1 - t0);
      info(0,"used %u of %u ms",tx,tlim);
      txtra += tlim - min(tlim,tx);
      sp++;
    }
    msgprefix(0,NULL);
  }
  msgprefix(0,NULL);
  setimer(0,time_virtual);

  planlen = min(planlen,Planlen);

  if (hindx2 < planlen) {
    sp = plan + hindx2;
    error_z(sp->nleg2,hindx2);
    if (sp->tuse > hiuse && sp->p0 < sp->p1) hisp = sp;
  }

  // use leftover time for highest bidder
  if (hisp != plan && txtra) {
    nleg1 = hisp->nleg2;
    nleg2 = hisp->nleg2;
    nleg3 = hisp->nleg3;
    nleg4 = hisp->nleg4;

    error_z(nleg1,nleg2);

    if (nleg2 == 0) dyn = 0;
    else if (nleg3 == 0) dyn = 1;
    else if (nleg4 == 0) dyn = 2;
    else dyn = 3;

    cost = src->costlim;

    tlim = txtra;
    info(0,"run dyn%u upto %u msec",dyn,tlim);
    switch(dyn) {
    case 0: msgprefix(0,"D0 %u-x-x %u",nleg1,cost); break;
    case 1: msgprefix(0,"D1 %u-%u-x %u",nleg1,nleg2,cost); break;
    case 2: msgprefix(0,"D2 %u-%u-%u %u",nleg1,nleg2,nleg3,cost); break;
    case 3:
    default: msgprefix(0,"D3 %u-%u-%u-%u %u",nleg1,nleg2,nleg3,nleg4,cost);
    }

    if (dyn == 2) {
      if (limitfac) txtra /= limitfac;
      else txtra *= 2;
      xplan[0].run = 1;
      xplan[0].nleg1 = nleg1;
      xplan[0].nleg2 = nleg2;
      xplan[0].nleg3 = nleg3;
      xplan[0].nleg4 = 0;
      xplan[0].tlim = txtra;
      xplan[0].p0 = 0;
      xplan[0].p1 = 0;

      xplan[1].nleg1 = 0;
      xplan[1].nleg2 = 0;
      xplan[1].nleg3 = 0;
      xplan[1].nleg4 = 0;
      info(0,"dyn2 %u-%u-%u %u",nleg1,nleg2,nleg3,cost);
      rv = srcdyn2_var(net,src,dep,arr,xplan,0,&txtra,&hindx2);
    } else {
      timelimit(src,tlim,desc,1);
      setimer(tlim,time_virtual);
      t0 = gettime_msec();

      switch (dyn) {
      case 0: rv = srcdyn0(net,src,dep,arr,nleg1); break;
      case 1: rv = srcdyn1(net,hisp,src,dep,arr,nleg1,nleg2); break;
      case 3: rv = srcdyn3(net,hisp,src,dep,arr,nleg1,nleg2,nleg3,nleg4); break;
      default: return 1;
      }
      t1 = gettime_msec();
      tx = (ub4)(t1 - t0);
      txtra = tlim - min(tlim,tx);
      info(0,"used %u of %u ms",tx,tlim);
    }
  }
  msgprefix(0,NULL);

  ub4 x;

  // mark which pass came within 20%
  cost = src->costlim;
  if (cost != hi32) {
    cost20 = cost + (cost * 20) / 100;
    sp = plan;
    while(sp->nleg1 && sp->cost > cost20) sp++;

    if (sp->nleg1) {
      nleg1 = sp->nleg1;
      nleg2 = sp->nleg2;
      nleg3 = sp->nleg3;
      nleg4 = sp->nleg4;
      x = nleg1 | (nleg2 << 3) | (nleg3 << 6) | (nleg4 << 9);
      if (x < Elemcnt(costleads)) costleads[x]++;
      fmtstring(src->costlead,"%u at %u-%u-%u-%u for %u",sp->cost,nleg1,nleg2,nleg3,nleg4,cost);
    } else info(0,"cost %u not found",cost);
    tlim = inftimes[nethistop];
  } else tlim = infnotimes[nethistop];

  ub4 runinf = dyncfg("search.srcinf",1,1);
  if (runinf == 0) return rv;

  // run srcinf
  if (limitfac) tlim *= limitfac;
  else tlim /= 2;

  info(0,"run srcinf upto %u+%u ms",tlim,txtra);
  tlim += txtra;
  if (tlim == 0) return rv;

  timelimit(src,tlim,"inf",1);
  setimer(tlim,time_virtual);
  msgprefix(0,"inf %u",src->costlim);
  rv = srcinf(net,src,dep,arr,nstophi);
  setimer(0,time_virtual);
  msgprefix(0,NULL);

  return rv;
}

// merge legs if on same route
static int mergelegs(struct trip *tp)
{
  ub4 len = tp->len;
  ub4 dur12,t1,t2,l1,l = 0;
  ub4 rid,tid,hop1,hop2,chop,gchop,dep,arr,gdep,garr;
  gnet *net = getnet();
  struct chop *chp;
  struct route *rp;
  int merged = 0;

  if (len < 2) return 0;

  if (globs.nomergeroute) return 0;

  ub4 *ridhops,*ridhopbase = net->ridhopbase;

  while (l + 1 < len) {
    l1 = l + 1;
    tid = tp->tid[l];
    if (tid == hi32 || tid != tp->tid[l1]) { l++; continue; }
    hop1 = tp->trip[l];
    hop2 = tp->trip[l1];

    if (hop1 >= net->chopcnt || hop2 >= net->chopcnt) { l++; continue; }
    dep = net->portsbyhop[hop1 * 2];
    arr = net->portsbyhop[hop2 * 2 + 1];
    if (dep >= net->portcnt || arr >= net->portcnt) { l++; continue; }

    if (hop1 < net->chopcnt) chp = net->chops + hop1;
    else { l++; continue; }

    rid = chp->rid;
    rp = net->routes + rid;

    ridhops = ridhopbase + rp->hop2pos;

    // get hop from rid,dep,arr. orgs in case of compound
    ub4 hopndx = 0,h1ndx = 0,h2ndx = 0;
    ub4 h,ghop1 = hi32,ghop2 = hi32;
    while (hopndx < rp->hopcnt && (ghop1 == hi32 || ghop2 == hi32)) {
      h = rp->hops[hopndx];
      if (h >= net->chopcnt) break;
      if (net->portsbyhop[h * 2] == dep) { ghop1 = h; h1ndx = hopndx; }
      if (net->portsbyhop[h * 2 + 1] == arr) { ghop2 = h;  h2ndx = hopndx; }
      hopndx++;
    }
    if (ghop1 == hi32 || ghop2 == hi32) { l++; continue; }
    else if (ghop1 >= net->hopcnt) { l++; continue; }
    else if (ghop2 >= net->hopcnt) { l++; continue; }
    if (ghop1 == ghop2) gchop = ghop1;
    else gchop = ridhops[h1ndx * rp->hopcnt + h2ndx];
    if (gchop >= net->chopcnt) { l++; continue; }

    chop = gchop;
    info(0,"merge leg %u+%u on equal tid %u, rid %u hop %u-%u = %u %u",l,l1,tid,rid,ghop1,ghop2,gchop,chop);
    if (chop >= net->chopcnt) { l++; continue; }
    info(0,"merge leg %u+%u on equal tid %u, rid %u hop %u-%u = %u",l,l1,tid,rid,ghop1,ghop2,gchop);

    tp->trip[l] = chop;
    t1 = tp->t[l]; t2 = tp->t[l1];
    dur12 = t2 - t1 + tp->dur[l1];
    tp->dur[l] = dur12;
    tp->info[l] = 1;
    if (len + 1 > l1) {
      memmove(tp->trip + l1,tp->trip + (l + 2),(len - l1 - 1) * sizeof(tp->trip));
      memmove(tp->t + l + 1,tp->t + l + 2,(len - l1 - 1) * sizeof(tp->t));
      memmove(tp->tid + l + 1,tp->tid + l + 2,(len - l1 - 1) * sizeof(tp->tid));
      memmove(tp->dur + l + 1,tp->dur + l + 2,(len - l1 - 1) * sizeof(tp->dur));
    }
    merged = 1;
    len--;
  }
  tp->len = len;
  return merged;
}

static void showstats(search *src)
{
  ub4 leg1,leg2,leg3,leg4,x,cnt,sumcnt = 0;

  info(0,"cumulative stats at query %u",src->cmdseq);

  for (x = 0; x < Elemcnt(costleads); x++) {
    cnt = costleads[x];
    if (cnt == 0) continue;
    sumcnt += cnt;
    leg1 = x & 7;
    leg2 = (x >> 3) & 7;
    leg3 = (x >> 6) & 7;
    leg4 = (x >> 9) & 7;
    info(Noiter,"  %u-%u-%u-%u: %u sum %u",leg1,leg2,leg3,leg4,cnt,sumcnt);
  }
}

static int tripreport(struct network *net,ub4 udep,ub4 uarr,ub2 usrdep,ub2 usrarr,struct trip *ptrip,char *buf,ub4 buflen,ub4 *ppos,ub4 utcofs,ub4 opts)
{
  struct port *pdep,*parr,*ports = net->ports;
  struct sport *psdep,*psarr,*sports = net->sports;
  struct chop *chp, *chops;
  struct route *rp,*routes = net->routes;
  struct chain *cp,*chains = net->chains;
  ub4 *trip = ptrip->trip;
  const char *rname,*dname,*aname,*mode = "";
  const char *suffix;
  ub4 rid,rrid,tid;
  ub4 leg,hop1,hop2,l,l1 = 0,l2 = 0,dep,arr = hi32;
  ub4 sdep,sarr;
  ub2 srdep,srarr;
  ub4 tdep,tarr,tsarr,thop,txtime,prvtarr = 0;
  ub4 dist,dist0,dt,fare;
  ub4 portcnt = net->portcnt;
  ub4 sportcnt = net->sportcnt;

  ub4 hopcnt,whopcnt,chopcnt,thopcnt;
  ub4 chaincnt;
  ub4 *portsbyhop;
  ub4 *hopdist;
  ub4 pos = *ppos;
  ub4 triplen = ptrip->len;
  ub4 *tports = ptrip->port;
  double dlat,dlon,alat,alon,fdist;
  ub4 walkspeed = net->walkspeed;  // geo's per hour
  double deplat,deplon,arrlat,arrlon,xarrlat,xarrlon,prvarrlat,prvarrlon,srdist;
  ub4 sdist;
  ub4 dstopid,astopid,dstopos,astopos;
  ub4 tripno,fltno1,alcode1,alcode2;
  int istaxi;
  int tzlocal = (utcofs >= 26 * 60);
  char fltno[32];
  char dstopstr[128];
  char astopstr[128];
  char tdname[128];
  char taname[128];
  char trname[128];
  char timbuf[64];

  ub4 showstopid = (opts & Stopid);
  ub4 showcoords = (opts & Coords);
  // ub4 showhtml = (opts & Rephtml);
  ub4 showiname = (opts & Intname);

  if (triplen == 0) { // trivial case: within same parent group
    if (udep == uarr && usrdep == usrarr) return 1;
    else if (udep != uarr) return warning(0,"nil trip for %u port net",portcnt);
    pdep = ports + udep;
    parr = ports + uarr;
    if (usrdep != hi16) {
      warncc(usrdep >= pdep->subcnt,0,"srdep %u subcnt %u",usrdep,pdep->subcnt);
      sdep = pdep->subofs + usrdep;
      psdep = sports + sdep;
      dname = psdep->name;
      dlat = psdep->rlat; dlon = psdep->rlon;
    } else {
      dname = pdep->name;
      dlat = pdep->rlat; dlon = pdep->rlon;
    }
    if (usrarr != hi16) {
      warncc(usrarr >= parr->subcnt,0,"srarr %u subcnt %u",usrarr,parr->subcnt);
      sarr = pdep->subofs + usrarr;
      psarr = sports + sarr;
      aname = psarr->name;
      alat = psarr->rlat; alon = psarr->rlon;
    } else {
      aname = pdep->name;
      alat = pdep->rlat; alon = pdep->rlon;
    }

    fdist = geodist(dlat,dlon,alat,alon,dname);
    dist = (ub4)fdist;
    dt = (dist * 60) / walkspeed;

    pos += mysnprintf(buf,pos,buflen,"sum\t\at%u\t\ag%u\t%u\t%u\t%s-%u\n",dt,dist,0,0,"t",0);

    pos += mysnprintf(buf,pos,buflen,"trip-dep\t\t%s\t\t\ar%f\t\ar%f\t%u\n",dname,dlat,dlon,1);
    pos += mysnprintf(buf,pos,buflen,"trip-rou\twalk\t\t0\t\ag%u\n",dist);

    pos += mysnprintf(buf,pos,buflen,"trip-arr\t\t%s\t\ar%f\t\ar%f\n",aname,alat,alon);

    *ppos = pos;

    info(0,"%s",buf);
    return 0;
  }

  if (triplen >= Nleg) {
    warn(0,"trip len %u above max %u",triplen,Nleg);
    triplen = Nleg;
  }

  if (tzlocal) pos += mysnprintf(buf,pos,buflen,"%s  tz = localtime\n",ptrip->desc);
  else pos += mysnprintf(buf,pos,buflen,"%s  tz = utc\au%u\n",ptrip->desc,utcofs);

  parr = NULL;
  arrlat = arrlon = 0;
  srarr = hi16;

  chops = net->chops;
  hopcnt = net->hopcnt;
  hopdist = net->hopdist;
  whopcnt = net->whopcnt;
  chopcnt = net->chopcnt;
  thopcnt = net->thopcnt;
  portcnt = net->portcnt;
  chaincnt = net->chaincnt;
  portsbyhop = net->portsbyhop;

  for (leg = 0; leg < triplen; leg++) {

    l = trip[leg];
    if (l >= whopcnt) return error(0,"leg %u hop %u >= %u",leg,l,whopcnt);
    dep = portsbyhop[2 * l];
    error_ge(dep,portcnt);
    pdep = ports + dep;
    dist = hopdist[l];
    sdep = sarr = hi32;
    chp = chops + l;
    rid = chp->rid;

    if (leg) {
      if (dep != arr) {
        if (l < whopcnt) return error(0,"leg %u hop %u dep %u not connects to preceding arr %u %s vs %s",leg,l,dep,arr,pdep->name,parr->name);
        else return error(0,"leg %u chop %u = %u-%u dep %u not connects to preceding arr %u %s vs %s",leg,l,l1,l2,dep,arr,pdep->name,parr->name);
      }
    } else if (dep != udep) return error(0,"trip starting with %u, not inital dep %u",dep,udep);

    arr = portsbyhop[2 * l + 1];
    error_ge(arr,portcnt);
    tports[leg] = dep;
    parr = ports + arr;

    prvarrlat = arrlat; prvarrlon = arrlon;

    if (leg == 0) srdep = usrdep; else srdep = ptrip->srdep[leg];

    srarr = ptrip->srarr[leg];

    if (srdep != hi16 && srdep >= pdep->subcnt) {
      warn(0,"leg %u srdep %u subcnt %u",leg,srdep,pdep->subcnt);
      srdep = hi16;
    }
    if (srdep != hi16) {
      sdep = pdep->subofs + srdep;
      if (sdep >= sportcnt) {
        warn(0,"sdep %u sportcnt %u",sdep,sportcnt);
        srdep = hi16;
      }
    }
    if (srdep != hi16) {
      psdep = sports + sdep;
      dname = showiname ? psdep->intname : psdep->name;
      dstopid = psdep->stopid;
      deplat = psdep->rlat;
      deplon = psdep->rlon;
      vrb0(0,"dname %s for srdep %u",dname,srdep);
    } else {
      dname = showiname ? pdep->intname : pdep->name;
      dstopid = pdep->stopid;
      deplat = pdep->rlat;
      deplon = pdep->rlon;
    }

    if (srarr != hi16) {
      warncc(srarr >= parr->subcnt,0,"srarr %u not in %u",srarr,parr->subcnt);
    }
    if (srarr != hi16) {
      sarr = parr->subofs + srarr;
      if (sarr >= sportcnt) {
        warn(0,"leg %u sarr %u sportcnt %u",leg,sarr,sportcnt); // todo
        srarr = hi16;
      }
    }
    if (srarr != hi16) {
      psarr = sports + sarr;
      aname = showiname ? psarr->intname : psarr->name;
      astopid = psarr->stopid;
      arrlat = psarr->rlat;
      arrlon = psarr->rlon;
      vrb0(0,"aname %s for srarr %u",aname,srarr);
    } else {
      aname = showiname ? parr->intname : parr->name;
      astopid = parr->stopid;
      arrlat = parr->rlat;
      arrlon = parr->rlon;
    }

    fmtstring(tdname," %.80s ",dname);
    fmtstring(taname," %.80s ",aname);

    dist0 = fgeodist(pdep,parr,1);
    tdep = ptrip->t[leg];
    if (tdep) {
      tarr = tdep + ptrip->dur[leg];
      tsarr = tarr + ptrip->sdur[leg];
    } else tarr = tsarr = 0;

    tid = ptrip->tid[leg];
    mode = modename(chp->kind);
    istaxi = (chp->kind == Taxi);
    if (rid != hi32) {
      rp = routes + rid;
      rname = rp->name;
      rrid = rp->rrid;
      fmtstring(trname,"%.60s",rname);
    } else {
      rrid = hi32;
      rname = "";
      fmtstring(trname,"%s",rname);
    }
    fare = ptrip->fares[leg];

    if (ptrip->info[leg] & 1) suffix = " *";  // merged
    else suffix = "";

    if (tid < chaincnt) {
      cp = chains + tid;
      tripno = cp->tripno;
    } else tripno = 0;

    if (tripno) {
      fltno1 = tripno & hi16;
      alcode1 = tripno >> 24;
      alcode2 = (tripno >> 16) & 0xff;
      if (alcode1 < '0' || alcode1 > 'Z') alcode1 = '?';
      if (alcode2 < '0' || alcode2 > 'Z') alcode2 = '?';
      fmtstring(fltno,"%c%c%04u",alcode1,alcode2,fltno1);
    } else *fltno = 0;

    hopmsg(Info,0,l,"leg %u dep %u.%u at \ad%u arr %u.%u at \ad%u tid %u fare %u %s %s",
        leg,dep,pdep->nda,tdep,arr,parr->nda,tarr,tid,fare,fltno,suffix);
    if (l < chopcnt) info(0,"  r.rid %u.%u route '%s'",rrid,rid,rname);

    // dep
    txtime = 0;
    if (dstopid && showstopid) dstopos = fmtstring(dstopstr," (%u)",dstopid);
    else dstopos = *dstopstr = 0;
    if (showcoords) {
      mysnprintf(dstopstr,dstopos,sizeof(dstopstr)," \ar%f,\ar%f",deplat,deplon);
    }

    if (tdep) fmtstring(timbuf,"\ad%u",min2llmin(tdep,utcofs,pdep->utcofs,pdep->dstonof));
    else *timbuf = 0;
    if (leg) { // add transfer time
      srdist = geodist(deplat,deplon,prvarrlat,prvarrlon,dname);
      sdist = (ub4)srdist;
      if (tdep && prvtarr) {
        if (tdep >= prvtarr) txtime = tdep - prvtarr;
        else warn(0,"leg %u depart \ad%u before previous arrival \ad%u",leg,tdep,prvtarr);
      }
      pos += mysnprintf(buf,pos,buflen,"trip-dep\t%s\t%s%s%s\t\ag%u\t\at%u\t\ar%f\t\ar%f\t%u\n",timbuf,tdname,dstopstr,suffix,sdist,txtime,deplat,deplon,leg+1);
    } else {
      pos += mysnprintf(buf,pos,buflen,"trip-dep\t%s\t%s%s%s\t\t\t\ar%f\t\ar%f\t1\n",timbuf,tdname,dstopstr,suffix,deplat,deplon);
    }

    // route: mode,fltno,name,dur,dist,cmt
    if (tdep && tarr && tarr >= tdep) thop = tarr - tdep;
    else thop = 0;
    if (rid == hi32) pos += mysnprintf(buf,pos,buflen,"trip-rou\t%s\t\t%s",mode,trname);
    else pos += mysnprintf(buf,pos,buflen,"trip-rou\t%s\t%s\t%s",mode,fltno,trname);
    pos += mysnprintf(buf,pos,buflen,"\t\at%u",thop);
    pos += mysnprintf(buf,pos,buflen,"\t%u",fare);
    if (dist != dist0) pos += mysnprintf(buf,pos,buflen,"\t\ag%u\t# (direct \ag%u)\n",dist,dist0);
    else pos += mysnprintf(buf,pos,buflen,"\t\ag%u\n",dist);

    // arr
    if (astopid && showstopid) astopos = fmtstring(astopstr," (%u)",astopid);
    else astopos = *astopstr = 0;
    if (showcoords) {
      mysnprintf(astopstr,astopos,sizeof(astopstr)," \ar%f,\ar%f",arrlat,arrlon);
    }

    if (tarr) fmtstring(timbuf,"\ad%u",min2llmin(tarr,utcofs,parr->utcofs,parr->dstonof));
    else *timbuf = 0;

    pos += mysnprintf(buf,pos,buflen,"trip-arr\t%s\t%s%s\t\ar%f\t\ar%f\n",timbuf,taname,astopstr,arrlat,arrlon);
    prvtarr = tsarr;

  } // each leg

  if (usrarr != hi16 && srarr != usrarr) {
    warncc(usrarr >= parr->subcnt,0,"srarr %u not in %u",usrarr,parr->subcnt);
    sarr = parr->subofs + usrarr;
    error_ge(sarr,sportcnt);
    psarr = sports + sarr;
    aname = psarr->name;
    astopid = psarr->stopid;
    xarrlat = psarr->rlat;
    xarrlon = psarr->rlon;

    fdist = geodist(arrlat,arrlon,xarrlat,xarrlon,aname);
    if (astopid && showstopid) astopos = fmtstring(astopstr," (%u)",astopid);
    else astopos = *astopstr = 0;
    if (showcoords) {
      mysnprintf(astopstr,astopos,sizeof(astopstr)," \ar%f,\ar%f",xarrlat,xarrlon);
    }
    pos += mysnprintf(buf,pos,buflen,"trip-xar\t\t%s%s\t\ag%u\t\ar%f\t\ar%f\n",aname,astopstr,(ub4)fdist,xarrlat,xarrlon);
  }

  *ppos = pos;

  tports[triplen] = arr;
  return 0;
}

// handle criteria and reporting
int plantrip(search *src,char *ref,ub4 xdep,ub4 xarr,ub4 nstoplo,ub4 nstophi)
{
  ub4 dep,arr,sdep,sarr;
  ub2 srdep,srarr;
  ub4 leg,t,t2;
  struct network *net = sn.net;
  ub4 portcnt = net->portcnt;
  ub4 sportcnt = net->sportcnt;
  struct port *parr,*pdep,*ports = net->ports;
  struct sport *psarr,*psdep,*sports = net->sports;
  ub4 deptmin,depttmin,deptmax;
  ub8 t0,dt,totcnt;
  ub4 utcofs,dsputcofs;
  ub4 resmax = sizeof(src->resbuf);
  struct trip *stp,*stp2;
  int same,rv;
  char dtstr[128];

  ub4 msgtid = src->msgtid;
  ub4 repopts = src->repoptions;

  gs_useacc = dyncfg("search.acc",1,1);

  if (xdep == xarr) return error(msgtid,"departure %u equal to arrival",xarr);

  if (xdep >= portcnt) {
    sdep = xdep - portcnt;
    if (sdep >= sportcnt) return error(msgtid,"departure %u not in %u subportlist",sdep,sportcnt);
    psdep = sports + sdep;
    dep = psdep->parent;
    srdep = psdep->seq;
    info(msgtid,"resolved dep %u into %u.%u id %u",sdep,dep,srdep,psdep->stopid);
  } else {
    srdep = hi16;
    dep = xdep;
  }

  if (xarr >= portcnt) {
    sarr = xarr - portcnt;
    if (sarr >= sportcnt) return error(msgtid,"arrival %u not in %u subportlist",sarr,sportcnt);
    psarr = sports + sarr;
    arr = psarr->parent;
    srarr = psarr->seq;
    info(msgtid,"resolved arr %u into %u.%u id %u",sarr,arr,srarr,psarr->stopid);
  } else {
    srarr = hi16;
    arr = xarr;
  }

  pdep = ports + dep;
  parr = ports + arr;

  info(msgtid,"dep %u.%u id %u %s/%s %f,%f infcon %u",dep,srdep,pdep->stopid,pdep->prefix,pdep->name,pdep->rlat * 180 / M_PI,pdep->rlon * 180 / M_PI,pdep->infconcnt);
  info(msgtid,"arr %u.%u id %u %s/%s %f,%f infcon %u",arr,srarr,parr->stopid,parr->prefix,parr->name,parr->rlat * 180 / M_PI,parr->rlon * 180 / M_PI,parr->infconcnt);

  inisrc(net,src,"src",0);
  src->dep = dep;
  src->arr = arr;

  if (pdep->valid == 0) {
    src->reslen = mysnprintf(src->resbuf,src->reslen,resmax,"dep %u %s is unconnected\n",dep,pdep->iname);
    return info(msgtid,"%s",src->resbuf);
  }
  if (parr->valid == 0) {
    src->reslen = mysnprintf(src->resbuf,src->reslen,resmax,"arr %u %s is unconnected\n",arr,parr->iname);
    return info(msgtid,"%s",src->resbuf);
  }

  if (dep == arr) {
    stp = src->trips;
    if (tripreport(net,dep,arr,srdep,srarr,stp,src->resbuf,resmax,&src->reslen,0,repopts)) return 1;
    info(msgtid,"reslen %u",src->reslen);
    return 0;
  }

  if (nstophi >= Nstop) { warning(msgtid,"limiting max %u-stop to %u", nstophi,Nstop); nstophi = Nstop - 1; }
  if (nstoplo > nstophi) { warning(msgtid,"setting min %u-stop to %u", nstoplo,nstophi); nstoplo = nstophi; }

  info(msgtid,"search dep %u arr %u between %u and %u stops, mode %u ref %s",dep,arr,nstoplo,nstophi,src->srcmode,ref);
  info(msgtid,"max walk distance \ag%u, summed \ag%u",src->walklimit,src->sumwalklimit);

  ub4 ttmin;
  ub4 *mintts = src->mintts;

  // supply implied transfer times
  ttmin = getmintt(mintts,Rail,Rail);
  mkmintt(mintts,Walkbit,Railbit,ttmin);
  mkmintt(mintts,Railbit|Busbit,Walkbit,0);
  ttmin = getmintt(mintts,Bus,Bus);
  mkmintt(mintts,Walkbit,Busbit,ttmin);
  ttmin = getmintt(mintts,Ferry,Ferry);
  mkmintt(mintts,Walkbit,Ferrybit,ttmin);
  mkmintt(mintts,Ferrybit,Walkbit,ttmin);

  ttmin = getmintt(mintts,Rail,Airint);
  mkmintt(mintts,Walkbit,Airintbit,ttmin);
  ttmin = getmintt(mintts,Rail,Airdom);
  mkmintt(mintts,Walkbit,Airdombit,ttmin);

  ttmin = getmintt(mintts,Airint,Rail);
  mkmintt(mintts,Airintbit,Walkbit,ttmin);
  ttmin = getmintt(mintts,Airdom,Rail);
  mkmintt(mintts,Airdombit,Walkbit,ttmin);

  enum txkind dmode,amode;
  for (dmode = Airint; dmode < Kindcnt; dmode++) {
    for (amode = Airint; amode < Kindcnt; amode++) {
      ttmin = getmintt(mintts,dmode,amode);
      info(V0,"%s-%s min tx time %u",modename(dmode),modename(amode),ttmin);
    }
  }

  ub4 tt0 = net->tt0;
  ub4 tt1 = net->tt1;
  ub4 gt0 = net->t0;

  src->lodist = hi32;
  src->timestop = hi32;

  src->geodist = fgeodist(pdep,parr,1);

  utcofs = utc12ofs(src->utcofs12);
  dsputcofs = utc12ofs(src->dsputcofs12);

  ub4 deptmin_cd = src->deptmin_cd;

  if (deptmin_cd == 0) deptmin = tt0;
  else {
    if (epochrange(FLN,deptmin_cd,"startdate")) return 1;
    deptmin = yymmdd2min(deptmin_cd,utcofs);
  }

  depttmin = hhmm2min(src->depttmin_cd);
  deptmin += depttmin;

  deptmin = max(deptmin,tt0);
  deptmin = min(deptmin,tt1);

  src->deptmid = deptmin;

  deptmin = max(deptmin - src->minhour * 60,net->tt0);
  deptmin = min(deptmin,tt1);

  src->dephwin = src->plushour;
  if (src->plushour == 0) deptmax = 0; // auto
  else {
    deptmax = src->deptmid + src->plushour * 60;
    deptmax = min(deptmax,tt1);
  }

  if (deptmin >= tt1) {
    src->reslen = mysnprintf(src->resbuf,src->reslen,resmax,"no trip found leaving at \ad%u\n",deptmin);
    return info(msgtid,"%s",src->resbuf);
  } else if (deptmax && (deptmax <= deptmin || deptmax <= tt0)) {
    src->reslen = mysnprintf(src->resbuf,src->reslen,resmax,"no trip found leaving at \ad%u - \ad%u\n",deptmin,deptmax);
    return info(msgtid,"%s",src->resbuf);
  } else if (deptmin <= gt0) {
    warn(0,"deptmin \ad%u, net t0 \ad%u",deptmin,gt0);
    deptmin = gt0 + 1;
  }

  src->deptmin = deptmin;
  src->udeptmax = deptmax;

  src->histop = nstophi;

  info(msgtid,"search dep %u arr %u on \ad%u-\ad%u \au%u %s to %s geodist \ag%u modes %x timescale %u",dep,arr,deptmin,deptmax,utcofs,pdep->name,parr->name,src->geodist,src->txmask,src->limitfac);

  t0 = src->queryt0 = gettime_msec();
  src->querytlim = hi64;
  src->tlim = hi32;
  src->costlim = hi32;
  gstat_evcnt = gstat_lkcnt = 0;

  rv = dosrc(net,nstoplo,nstophi,src,ref);

  dt = gettime_msec() - t0;

  info(CC0 | msgtid,"altlim 2 %u for %d",src->stat_altlim2,rv);
  info(CC0 | msgtid,"altlim 3 %u for %d",src->stat_altlim3,rv);

  if (dt > 2000) fmtstring(dtstr,"%u.%u ",(ub4)(dt / 1000),(ub4)(dt % 1000) / 10);
  else fmtstring(dtstr,"%u milli",(ub4)dt);

  ub4 duriv = (ub4)min(dt / 1000,Elemcnt(src->querydurs) - 1);
  src->querydurs[duriv]++;
  if (dt > src->querymaxdur) {
    src->querymaxdur = dt;
    src->querymaxdep = dep;
    src->querymaxarr = arr;
  }

  if (getres(src,net) == 0) {
    src->notrips++;
    src->reslen += mysnprintf(src->resbuf,src->reslen,resmax,
      "no trip found in %u stops ref %s - %s\n\nsearched \ah%lu combi\as with \ah%lu,\ah%lu departure\as in %ssec\n",
       src->hisrcstop,pdep->prefix,parr->prefix,src->combicnt,gstat_lkcnt,gstat_evcnt,dtstr);
    info(msgtid,"%s",src->resbuf);
    return info(msgtid,"no route or time found for %u stop\as",nstophi);
  }

  ub4 ntrip = src->ntrip;
  if (ntrip == 0) return warn(msgtid,"no trips for %u stop\as",nstophi);
  else if (ntrip > 1) src->reslen += mysnprintf(src->resbuf,src->reslen,resmax,"%u trip\as\n",src->ntrip);

  stp = src->trips;

  for (t = 0; t < ntrip; t++) {
    stp = src->trips + t;
    if (stp->len == 0) {
      info(msgtid,"trip #%u is empty",t);
      continue;
    }
    same = 0;
    for (t2 = 0; t2 < t; t2++) {
      stp2 = src->trips + t2;
      same = sametrip(stp,stp2);
      if (same) { info(msgtid,"skip identical trip %u for %u",t2,t); break; }
    }
    if (same) continue;
    while (mergelegs(stp)) ;
    info(msgtid,"%u-leg trip %u of %u",stp->len,t,src->ntrip);
    if (tripreport(net,dep,arr,srdep,srarr,stp,src->resbuf,resmax,&src->reslen,dsputcofs,repopts)) warn(msgtid,"error in %u-leg trip %u",stp->len,t);
  }

  src->reslen += mysnprintf(src->resbuf,src->reslen,resmax,
    "\nstat\tsearched \ah%lu combi\as with \ah%lu,\ah%lu time\as in %ssec  %s ref %s %s\t%u\t%u\n",
    src->combicnt,gstat_lkcnt,gstat_evcnt,dtstr,src->costlead,pdep->prefix,parr->prefix,net->feedlostamp,net->feedstamp);

  msg_write(src->resbuf,src->reslen);
  errorcc(src->reslen + 20 > resmax,msgtid,"result buffer truncated at %u",resmax);

  ub4 *tmo = src->stat_tmo;
  ub4 *evstp = src->addstat;
  info(msgtid,"timeouts: dyn0 %u dyn1 %u dyn2 %u dyn3 %u",tmo[0],tmo[1],tmo[2],tmo[3]);

  info(msgtid,"limits d1 %u d2 %u,%u d3 %u,%u",src->midlim1cnt,src->mid1limcnt2,src->mid2limcnt2,src->mid1limcnt3,src->mid3limcnt3);

  info(msgtid,"ev stats d0 \ah%u dn \ah%u,\ah%u ev \ah%u tx \ah%u ttx \ah%u add \ah%u",evstp[0],evstp[1],evstp[2],evstp[3],evstp[4],evstp[5],evstp[6]);
  // info(msgtid," %u mkdeps %u reuse",src->de_cnt,src->de_usecnt);

  ub4 cnt,*dsp = src->dyn2stat;
  ub4 stop1,stop2,stop3;

  for (stop3 = 0; stop3 < Netn; stop3++) {
    for (stop2 = 0; stop2 < Netn; stop2++) {
      for (stop1 = 0; stop1 < Netn; stop1++) {
        cnt = dsp[stop3 * Netn * Netn + stop2 * Netn + stop1];
        info(CC0|msgtid,"%u bound\as for dyn2 %u-%u-%u",cnt,stop1+1,stop2+1,stop3+1);
      }
    }
  }
  if (src->cmdseq % 100) return 0;
  showstats(src);
  return 0;
}

void inisearch(void)
{
  msgfile = setmsgfile2(__FILE__,Msgfile_noiter);
  iniassert();
  vrbena = (getmsglvl() >= Vrb);
}
