// net3.h - precompute 3-stop connections

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2015 Joris van der Geer.
 */


extern void ininet3(void);
extern int mknet3(struct network *net,ub4 varlimit,ub4 var12limit,ub4 altlimit,ub4 cntonly,ub4 netstop);
