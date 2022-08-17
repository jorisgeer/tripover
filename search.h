// search.h - defines for actual journey search

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2015 Joris van der Geer.
 */

enum srcmodes { Srclotime, Srchitime, Srcxtime, Srclofare, Srchifare, Srcxfare, Srcmodecnt };

#define Planlen 128
#define Ntop 8
#define Nalt 64

#define Nevres 32

enum Repoption { Stopid=1,Coords=2,Rephtml=4,Intname=8 };

struct trip {
  ub4 trip[Nleg];
  ub4 port[Nleg+1];  // destination port list
  ub4 t[Nleg];       // dep time
  ub4 tid[Nleg];
  ub4 dur[Nleg];
  ub4 sdur[Nleg];
  ub4 info[Nleg];
  ub2 srdep[Nleg];
  ub2 srarr[Nleg];
  ub4 fares[Nleg];

  char desc[256];
  ub4 desclen;

  ub4 len; // nleg
  ub4 cost;
  ub4 dist;
  ub4 dt;
  ub4 fare;
};

// store event info for a single trip
struct srcres {
  ub4 hop[Nleg];
  ub4 td[Nleg];
//  ub4 tat[Nleg];
  ub8 x[Nleg];
  ub4 cost;
  ub2 nleg;
};

struct srcxres {
  ub2 ndyn;
  ub4 nleg0,nleg1,nleg2,nleg3;
  ub4 i0,i1;
  ub4 dt;
};

// port and hop refs are global
struct srcctx {
  ub4 msgtid;

  char desc[256];

  // result
  char resbuf[Ntop * Nleg * 3 * 512];
  ub4 reslen;
  struct trip trips[Ntop];
  ub4 ntrip;
  ub4 hisrcstop;

  // main search args
  ub4 cmdseq;
  ub4 dep,arr;
  ub4 ntop;

  // search params
  ub4 deptmin,deptmax,deptmid,udeptmax,dephwin;
  ub4 deptmin_cd,depttmin_cd;
  ub4 plushour,minhour;
  ub4 utcofs12,dsputcofs12;
  ub4 lostop,histop,nethistop;
  ub4 walklimit,sumwalklimit,walkspeed;
  ub4 stop;
  ub4 costperstop;
  enum srcmodes srcmode;
  ub4 limitfac;

  ub4 mintts[256];
  ub1 txmask;

  // report options
  ub4 repoptions;

  // search time
  ub8 querytlim,queryt0;
  ub4 tlim;
  const char *limitdesc;

  // workspace
  struct srcres curres[Nalt],res[Nevres];
  struct srcxres curxres[Nalt];
  ub4 rescnt;
  ub4 locost;
  ub4 lores;
  ub4 topndx;
  ub4 altpos;

  ub4 lodt,hidt;
  // ub4 locost;
  ub4 costlim;
  ub4 lodist;
  ub4 hidist;
  ub4 geodist;
  ub4 timestop,diststop;
  ub4 dwleg,dwhop,dwday,dwhr;
  char dwinfo[128];

  // support dep event reuse
  ub4 de_prvhop;
  ub4 de_prvwin;
  ub4 de_costlim;

  ub1 *infconns; // [portcnt * Nleg]
  ub4 *infdaconns;  // [portcnt * Nleg]

  // store current best trip
  ub4 curdts[Nleg];
  ub4 curdurs[Nleg];
  ub4 cursdurs[Nleg];
  ub4 curts[Nleg];
  ub4 curcosts[Nleg];
  ub4 curtids[Nleg];
  ub4 curfares[Nleg];
  ub4 cursdeps[Nleg];
  ub4 cursarrs[Nleg];
  ub4 curt; // shorthand for overall props
  ub4 curhwin;
  char costlead[64];
  ub8 combicnt;

  ub4 stat_noprv;
  ub4 stat_nxtlim;
  ub4 stat_nxt0,stat_nxt3;
  ub4 stat_altlim2,stat_altlim3;
  ub4 stat_tmo[8];
  ub4 addstat[16];
  ub4 costndx;
  ub4 dyn2stat[Netn * Netn * Netn];
  ub4 errcnt;
  ub4 midlim1cnt,mid2limcnt2,mid1limcnt2,mid1limcnt3,mid3limcnt3;
  ub4 de_cnt,de_usecnt;

  // stats for iter test
  ub4 querydurs[1000];
  ub8 querymaxdur;
  ub4 querymaxdep,querymaxarr;
  ub4 notrips;

  ub4 nleg;

  ub4 hops[Nleg];

  ub4 dcnts[Nleg];   // #events in dev[leg]

  ub4 costcurs[Nleg];  // low cost (=biased dt) for [0.. curleg]

  ub4 devcurs[Nleg]; // dev index for above
  ub4 devcurs2[Nleg]; // idem, next low

  ub4 devttmin[Nleg];  // effective min txtime

  ub2 *depevs[Nleg]; // candidate event+attr store: time,tid,dt,dur,cost

  ub2 *evpool;
};
typedef struct srcctx search;

extern void inisearch(void);
extern void inisrc(gnet *net,search *src,const char *desc,ub4 arg);
extern int plantrip(search *src,char *ref,ub4 dep,ub4 arr,ub4 nstoplo,ub4 nstophi);
extern int loadplans(void);
