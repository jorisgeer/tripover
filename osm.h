// osm.h - handle openstreetmap data

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2015-2016 Joris van der Geer.
 */

#define Osmgeoscale (1000 * 1000 * 10)

enum osmopt { Osm_none, Osm_show = 1 };

enum osmodes { Osnil = 0, Osfoot = 1,Osbike = 2,Oscar = 4,Osmodecnt = 8 };

struct osmres {
  ub4 dist;
  ub4 time;
  ub4 cnt;
};

struct osminfo {
  ub4 nidcnt;
};

extern void *readosm(const char *name,struct osminfo *oi);
extern ub4 lookupnid(void *von,ub4 ilat,ub4 ilon,enum osmodes mode,ub4 *pdist);
extern int osmplan(void *vosm,ub4 depnid,ub4 arrnid,ub4 distlim,enum osmodes mode,enum osmopt opts,struct osmres *res);
extern int osmprofile(void *vosm,ub4 depnid,ub4 *nid2port,ub1 *portdup,ub4 portcnt,ub4 *ports,ub8 *portdts,ub4 distlim10,enum osmopt opts,struct osmres *res);

extern void osmstats(void *vosm);

extern int freeosm(void *vosm);

extern int iniosm(void);
