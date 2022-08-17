// osmint.h - handle openstreetmap data, internal defines

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2015-2016 Joris van der Geer.
 */

#define Njoin 32

struct node {
  ub4 ilat,ilon;
  double rlat,rlon;
  ub4 wid;  // first way if member of multiple
  ub4 jid;  // join id if applicable
};

struct way {
  ub4 nofs;
  ub2 ncnt;
  ub2 jcnt;
  ub1 modes;
  ub2 speed;

  // neigbour joins
  ub4 jofs;

  char name[32];
};

struct join {
  ub4 ways[Njoin];
  ub2 waypos[Njoin];
  ub4 wcnt;
  ub4 nid;
};

struct onet {

  // input net
  ub4 nidcnt,waycnt,joincnt,wnidcnt;
  ub4 nlstlen;
  struct node *nodes;
  struct way *ways;
  struct join *joins;
  ub4 *nidlst;
  ub4 *nidgeo;

  // workspace
  ub4 *joinlst;
  ub2 *joinposlst;
  ub4 *lst1,*lst2; // [joincnt]
  ub4 *map; // [joincnt]
  ub8 *dists; // [joincnt]
  ub4 *times; // [joincnt]
  ub4 *mapuse; // [joincnt]
  ub4 *jidref; // [joincnt]
  ub4 sortcnts[Osmodecnt];
  ub4 *latsorts[Osmodecnt],*lonsorts[Osmodecnt];
  ub4 *latsortidxs[Osmodecnt],*lonsortidxs[Osmodecnt];

  // stats
  ub4 plancnt,noplancnt;
};
