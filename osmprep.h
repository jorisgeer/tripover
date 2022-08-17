// osmprep.h - prepare openstreetmap data

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2015-2016 Joris van der Geer.
 */

struct bucket {
  ub4 sofs;
  ub4 slen;
  ub4 code;
  ub4 data;
};

struct hashtab {
  ub4 len;
  ub4 eqlen;
  ub4 maxeq;
  ub4 itemcnt;
  char *strpool;
  ub4 spoollen,sofs;
  struct bucket *bkts;
  block bktmem;
  block strmem;
  const char *desc;
};
typedef struct hashtab hash;

struct node {
  ub4 rid;
  sb4 ilat,ilon;
  double rlat,rlon;
};

struct way {
  ub4 rid;
  ub4 nofs;
  ub2 nodecnt;
  ub1 closed;
  ub1 area;
  ub1 joined;
  ub1 car,foot,access;
  ub2 speed;
  char name[32];
};

#define TNjoin 64

struct tjoin {
  ub4 ways[TNjoin];
  ub2 waypos[TNjoin];
  ub4 wcnt;
  ub4 nid;
};
