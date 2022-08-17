// condense.h - make network more dense

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2015 Joris van der Geer.
 */

extern void ininetev(void);

extern ub4 estdur_3(lnet *net,ub4 h1,ub4 h2,ub4 h3,ub4 *pdtlo,ub4 *pdthi,ub4 *ptypdt);
extern ub4 estdur_2(lnet *net,ub4 h1,ub4 h2,ub4 *pdtlo,ub4 *pdthi,ub4 *ptypdt);

extern int prepnetev(lnet *net);
extern int dupevs(lnet *net,ub4 hop1,ub4 hop2);
extern void estdur2_stats(ub4 tid);
extern void estdur3_stats(ub4 tid);
extern ub4 lotx2(lnet *net,ub4 hop1,ub4 hop2,ub4 *phitx);
