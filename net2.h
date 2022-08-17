// net2.h - precompute 2-stop connections

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2015 Joris van der Geer.
 */


extern void ininet2(void);
extern int mknet2(struct network *net,ub4 varlimit,ub4 var12limit,ub4 cntonly,ub4 netstop);
