// gtfsprep.h - prepare gtfs feeds

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2015-2016 Joris van der Geer.
 */

#define Nearstop 64
#define Namelen 128

struct gtstop {
  bool valid;
  ub4 id,pid,stopid,prestopid,prepstopid;
  ub4 linno;

  ub4 gidofs,codeofs,parentofs,descofs;
  ub4 gidlen,codelen,namelen,inamelen,parentlen,desclen,tznamlen;
  ub4 pnamelen;
  char *pnameref;
  bool isparent,hasparent;
  ub4 loctype;
  ub4 ilat,ilon;
  ub4 coloc;
  double lat,lon,rlat,rlon;
  ub4 nearcnt,enearcnt,stncnt;
  ub4 nears[Nearstop];
  ub4 group,iparent;
  ub4 iter,subiter;
  char name[Namelen];
  char iname[Namelen];
  char tzname[32];
  char parentname[Namelen];
  ub4 geondx;
};

struct geostop {
  ub4 id;
  ub4 ilat,ilon;
  double lat,lon,rlat,rlon;
  ub4 utcofs12;
  ub4 pop;
  ub4 namelen,tzlen;
  ub1 isplace;
  char name[64];
  char tzname[32];
};

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
  ub4 fln;
  const char *desc;
};
typedef struct hashtab hash;

struct route {
  ub4 aid;
  ub4 type;
  ub4 tripcnt;
  ub4 skipto;
  ub4 linno;
  ub4 eqid,eqcnt;
  char name[256];
  char rrid[128];
  char agency[128];
};

struct iroute {
  ub4 rid;  // original from trip
  ub4 type;
  char id[64];
  char name[128];
};

struct tripstop {
  ub2 seq;
  ub4 tdep,tarr;
  ub4 stopid;
  ub4 prestopid;
  ub4 stid; // back link to stoptime
  ub4 linno;
};

struct trip {
  ub4 tid,rid,irid;
  ub4 type;
  ub4 bid;
  ub4 sid;
  ub4 join,join2;
  ub4 loseq,hiseq;
  ub4 lostop,histop;
  ub4 lotarr,hitdep;
  ub4 repiv,repstart;
  ub4 loprestopid,hiprestopid;
  ub4 len;
  ub4 stopofs,rridofs;
  ub4 linno;
  ub8 seqsum,timesum;

  ub4 orgtidpos,orgridpos,rridpos,sidpos,headsignpos;

  ub2 orgtidlen,orgridlen,rridlen,sidlen,headsignlen;

  char flno[8];
  char name[64];

  char iroute[16+16+4+16+32];

  int watch;
};

#define Stop_idlen 126

struct stoptime {
  ub4 tid;
  ub4 linno;
  ub4 prestopid;
  ub4 stopid;
  ub4 rstopid;
  char *stop_id;

  ub2 seq;
  ub4 tdep,tarr;
};

struct gtfsnet {
  ub4 agencycnt;
  ub4 calendarcnt;
  ub4 caldatescnt;
  ub4 routecnt;
  ub4 xfercnt;
  ub4 iroutecnt;
  ub4 stopcnt;
  ub4 prestopcnt;
  ub4 tripcnt;
  ub4 freqcnt;
  ub4 stoptimescnt;
  ub4 stopseqcnt;
  ub4 geostopcnt;
  ub4 geopopcnt;
  block agencymem;
  block calendarmem;
  block caldatesmem;
  block routemem;
  block xfermem;
  block stopmem,estopmem;
  block tripmem,stripmem;
  block freqmem;
  block stoptimesmem;
  block stopseqmem;
  block iroutemem;
  char *agencylines;
  char *calendarlines;
  char *caldateslines;
  char *routelines;
  char *xferlines;
  char *stoplines;
  char *triplines,*striplines;
  char *freqlines;
  char *stoptimeslines;
  char *stopseqlines;
  char *iroutelines;
  char summarylines[1024];
  ub4 agencylinepos;
  ub4 calendarlinepos;
  ub4 caldateslinepos;
  ub4 routelinepos;
  ub4 xferlinepos;
  ub4 stoplinepos;
  ub4 triplinepos,striplinepos;
  ub4 freqlinepos;
  ub8 stoptimeslinepos;
  ub8 stopseqlinepos;
  ub4 iroutelinepos;
  ub4 summarylinepos;

  hash *agencyids;

  hash *serviceids;

  hash *routeids,*norouteids;
  struct route *routes;
  struct iroute *iroutes;
  hash *tripids,*notripids;
  hash *blockids;
  struct trip *trips;

  hash *stopids;
  hash *prestopids;
  struct gtstop *prestops;
  ub4 *latsort,*lonsort;
  ub4 *latsortidx,*lonsortidx;
  ub4 *namlatsort,*namlonsort;
  ub4 *namlatsortidx,*namlonsortidx;

  struct geostop *geostops;

  iadrbase net0;

};
typedef struct gtfsnet gtfsnet;
