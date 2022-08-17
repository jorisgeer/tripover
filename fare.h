// fare.h - handle fare/seat availiability for reserved transport

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2015 Joris van der Geer.
 */

extern void inifare(void);
extern int fareupd(gnet *net,ub4 rid,ub4 hop1,ub4 hop2,ub4 chop,ub4 t,ub4 mask,ub4 nfare,ub4 *fares);
ub4 mkfare(struct chop *hp);
