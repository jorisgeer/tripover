// event.h - time events

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2015 Joris van der Geer.
 */

extern void inievent(int pass);

extern void showxtime(struct timepatbase *tp,ub8 *xp,ub4 xlim);

extern ub4 fillxtime(netbase *net,ub4 hop,struct timepatbase *tp,ub8 *xp,ub1 *xpacc,ub4 xlen,ub4 gt0,struct sidbase *sp,ub1 *daymap,ub4 tdeprep,ub4 repstart,ub4 repend,ub4 tid,const char *desc);
extern ub4 fillxtime2(struct timepatbase *tp,ub8 *xp,ub1 *xpacc,ub4 xlen,ub4 gt0,struct sidbase *sp,ub1 *daymap,ub4 maplen,ub4 tdeprep,ub4 repstart,ub4 repend,ub4 dtid,ub4 dur,ub4 srdep,ub4 srarr,ub4 evcnt);
//extern ub4 findtrep(struct timepatbase *tp,ub8 *xp,ub1 *xpacc,ub8 *xp2,ub4 xlim,ub4 evcnt);
extern ub4 filltrep(netbase *net,struct chainbase *chbase,ub4 chaincnt,ub4 rid,block *evmem,struct timepatbase *tp,ub8 *xp,ub1 *xpacc,ub4 xlim);
extern ub4 filterxtime(struct timepatbase *tp,ub8 *xp,ub1 *xpacc,ub4 xlim,ub4 period0,ub4 period1);

extern void clearxtime(struct timepatbase *tp,ub8 *xp,ub1 *xpacc,ub4 xlim);

// around 30 min
#define Baccshift 5
