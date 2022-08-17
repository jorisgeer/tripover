// netio.h

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014 Joris van der Geer.
 */

extern int net2pdf(netbase *net);
extern void ininetio(void);
extern int net2ext(netbase *net);
extern int readextnet(netbase *net,const char *dir);
extern int wrportrefs(netbase *net,ub4 *bbox);
