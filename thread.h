// thread.h - thread management

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2015 Joris van der Geer.
 */

extern int newthread(ub4 tid,void *(*startfn)(void *),void *arg);
extern void *jointhread(ub4 tid);
extern void *joinanythread(void);
extern void threadstart(ub4 tid);
extern void threadend(ub4 tid);

extern void inithread(void);
