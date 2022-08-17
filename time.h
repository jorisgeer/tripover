// time.h

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2015 Joris van der Geer.
 */

#define Epochyear 2000
#define Epoch 20000101

// 1-1-2000 = sat
#define Epochwday 5

// time horizon
#define Erayear 2020
#define Era  20200101
#define Era1 20191231

// c11 langage only
#if defined  __STDC_VERSION__ && __STDC_VERSION__ >= 201101
  _Static_assert(Epochyear > 1969,"time before 1970 not handled");
  _Static_assert(Epochyear < 2100,"time after  2100 not handled");
  _Static_assert(Epochyear < Erayear,"must have a time span");
  _Static_assert(Erayear - Epochyear < 100,"time span too large");
  _Static_assert(Erayear > Epochyear,"time span too small");
#endif

#define lmin2min(lmin,utcofs) lmin2minfln(FLN,(lmin),(utcofs))

static inline ub4 lmin2mini(ub4 lmin,ub4 utcofs)
{
  if (lmin < utcofs) return lmin;
  else if (lmin == utcofs) return 0;
  else if (utcofs < 12 * 60) return lmin + (12 * 60 - utcofs);
  else if (utcofs > 12 * 60) return lmin - (utcofs - 12 * 60);
  else return lmin;
}

#define cd2day(c) cd2dayfln(FLN,(c))
#define day2cd(c) day2cdfln(FLN,(c))

extern ub4 gettime_sec(void);
extern ub8 gettime_msec(void);
extern ub8 thrtime_usec(void);
extern int setimer(ub4 msec,bool virtual);
extern int setthtimer(ub4 tid,ub4 msec);
extern int rmthtimer(ub4 tid);
extern int isexpired(ub4 tid);
extern int isalarm(void);

extern int epochrange(ub4 fln,ub4 cd,const char *name);
extern ub4 epochlim(ub4 day);

extern ub4 sec70toyymmdd(ub4 secs,ub4 prec,char *dst,ub4 dstlen);
extern ub4 yymmdd2min(ub4 cd,ub4 utcofs);
extern ub4 lmin2cd(ub4 min);
extern ub4 min2wday(ub4 min);
extern ub4 min2lmin(ub4 min,ub4 utcofs);
extern ub4 min2llmin(ub4 min,ub4 utcofs,ub4 locofs,ub4 dstonof);
extern ub4 lmin2minfln(ub4 fln,ub4 lmin,ub4 utcofs);
extern ub4 utc12ofs(ub4 uo12);
extern ub4 cdday2wday(ub4 cd);
extern ub4 cd2dayfln(ub4 fln,ub4 cd);
extern ub1 indst(ub4 t,ub4 dstonof);
extern ub4 day2cdfln(ub4 fln,ub4 day);
extern ub4 hhmm2min(ub4 ct);
extern ub4 nix2min(ub4 xmin);

extern void initime(int iter);
extern void exitime(void);
