// thread.c - thread management

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2015 Joris van der Geer.
 */

#include <pthread.h>

#include "base.h"
#include "thread.h"
#include "os.h"

static ub4 msgfile;
#include "msg.h"

static pthread_t ptids[Nthread];
static int runtids[Nthread];
static int endtids[Nthread];
static ub4 hitid;

int newthread(ub4 tid,void *(*startfn)(void *),void *arg)
{
  int rv;

  error_ge(tid,Nthread);

  hitid = max(hitid,tid);
  rv = pthread_create(ptids + tid,NULL,startfn,arg);
  if (rv) return oserror(0,"cannot create thread %u",tid);
  else return 0;
}

void *jointhread(ub4 tid)
{
  int rv;
  void *trv;

  error_ge(tid,Nthread);

  rv = pthread_join(ptids[tid],&trv);
  if (rv) { oserror(0,"cannot join thread %u",tid); return NULL; }
  if (trv == NULL) error(0,"cannot join thread %u",tid);
  globs.tids[tid] = runtids[tid] = 0;
  return trv;
}

void *joinanythread(void)
{
  ub4 tid;
  int rv;
  void *trv;

  for (tid = 0; tid <= hitid; tid++) {
    if (endtids[tid] == 0) continue;
    endtids[tid] = 0;
    rv = pthread_join(ptids[tid],&trv);
    if (rv == 0) {
      globs.tids[tid] = runtids[tid] = 0;
      if (trv == NULL) error(0,"cannot join thread %u",tid);
      return trv;
    }
    oserror(0,"cannot join thread %u",tid);
    return NULL;
  }
  return NULL;
}

// to be called from started thread
void threadstart(ub4 tid)
{
  error_ge(tid,Nthread);
  globs.tids[tid] = runtids[tid] = 1;
  endtids[tid] = 0;
}

void threadend(ub4 tid)
{
  error_ge(tid,Nthread);
  endtids[tid] = 1;
}

void inithread(void)
{
  iniassert();
}
