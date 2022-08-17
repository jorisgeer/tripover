// netbase.h - primary network defines

/* structures and definitions for the primary network components :

 - port ( aka stop, station or hub ).
 - hop ( direct connection between 2 ports )
 - route ( sequence of hops, e.g. for rail and bus )
 - timetable ( aka schedule )
 - service. e.g. route for rail+bus, single hop for air

   examples:

   air
     port = Zaventem
     hop = AMS to BRU

  rail
    port = Leuven
    hop = Bruxelles Nord to Mechelen
    route = Amsterdam centraal to Paris Nord

  bus
    port = Bardon
    hop = Elimbah to Beerburrum
    route = 444N

   Derived, secondary data is mostly in net.h
 */

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2017 Joris van der Geer.
 */

todo no base level

enum txbkind { Unknownb,Airintb,Airdomb,Railb,Busb,Ferryb,Taxib,Walkb,Kindcntb };

#define Portnamelen 256

// in minutes: typical max 7 days ~ 10k  14b = 11d
// +5b for 2-seconds  -> 21 for 24d
// dayno if ref
#define Bdurbits 14

// in minutes: typical timespan is few weeks: 3 * 7 * 1440 ~ 32k  18b = 177d
// +5b for 2 seconds -> 22 for 100d
#define Btimbits 18

// 1440 * 90 / 5  = 25k  -> 5b for flights only
#define Bdtidbits 10

// next pos at 4-hour,day,week intervals
#define Bsrdabits 16

sassert(Bdurbits + Btimbits + Bdtidbits + Bsrdabits < 64,"evbits <= 64") sassert_end

#define Btimlim ((1U << Btimbits) - 1)
#define Bdurlim ((1U << Bdurbits) - 1)
#define Bdtidlim ((1U << Bdtidbits) - 1)
#define Bsrdalim ((1U << Bsrdabits) - 1)

// tim | srda | dtid | dur
#define Bdtidshift Bdurbits
#define Bsrdahift (Bdtidbits + Bdurbits)
#define Btimhift (Bsrdabits + Bdtidbits + Bdurbits)

struct portbase {
  ub4 magic;
  ub4 id;
  ub4 cid;     // constant at net changes
  ub4 stopid;

  char name[Portnamelen];
  char intname[Portnamelen];
  char iname[256];
  char prefix[64];
  ub4 namelen,intnamelen;
  ub4 prefixlen;

  ub4 ndep,narr;

  ub4 subcnt,subofs;

  bool parentsta;

  bool air,rail,bus,ferry,taxi,geo;
  ub4 modes;

  ub4 lat,lon;
  double rlat,rlon;

  ub4 utcofs,dstonof;

  ub4 size;
};

struct subportbase {
  ub4 id;      // index in net.ports
  ub4 pid;
  ub4 subid;
  ub4 stopid;
  ub4 cid;     // constant at net changes
  ub4 parent;

  char name[Portnamelen];
  char intname[Portnamelen];
  ub4 namelen,intnamelen;

  ub4 ndep,narr;
  bool air,rail,bus,ferry,taxi;
  ub4 modes;

  ub4 lat,lon;
  double rlat,rlon;

  ub2 seq;
};

struct chainhopbase {
  ub4 hop;
  ub4 chain;
  ub4 tdep,tarr;
  ub4 midur;
  ub4 seq;
  ub4 srda;
};

struct chainbase {
  ub4 hoprefs;
  ub4 rhopcnt;
  ub4 rtid;
  ub4 dtid;
  ub4 tripno;
  ub4 rrid;
  ub4 rid;
  ub4 dep;
  ub4 hopcnt;
  ub4 hopofs;
  ub4 lotdep,lotarr,hitdep,hitarr;
  ub4 lotdhop,hitahop;
  ub4 firsthop;
  ub8 code;
};

struct ridebase {
  ub4 rtid;
  char name[128];
  ub2 namelen;
  ub2 cnt;
};

struct agencybase {
  ub4 raid,aid;
  char name[128];
  ub2 namelen;
  ub2 ridcnt;

  ub4 utcofs;     // minutes east from utc + 12h
  ub4 dstonof;
};

struct timepatbase {
  ub4 hop;
  ub4 utcofs;

  ub4 gt0;
  ub4 t0,t1;   // actual event range in min relative to gt0
  ub4 lodur,hidur,midur,avgdur,duracc;
  ub4 evcnt;
  ub4 evofs;
  int overtake;
  ub4 overtakehi;
};

struct hopbase {
  ub4 magic;
  ub4 id;       // from gtfstool

  char iname[128];
  char name[128];
  ub4 namelen;

//  ub2 valid;
  ub2 fare;
  ub2 varsda;
  ub2 srdep,srarr;

  enum txbkind kind;

  ub4 dep,arr;   // parent

  ub4 rrid,rid;
  ub4 rhop;  // relative within rid

  struct timepatbase tp;
  ub4 timespos;
  ub4 timecnt;
  ub4 evcnt;
  ub4 dupevcnt;
  ub4 t0,t1;   // overall gross date range of timetable : t1 exclusive
  ub4 dist;

  ub4 carrier;
};

struct routebase {
  ub4 magic;
  ub4 id;       // index in net.routes
  ub4 cid;
  ub4 rrid;

  ub4 rtype;
  ub4 aid;
  ub2 reserve;
  ub2 fare;

  enum txbkind kind;

  char name[256];
  ub4 namelen;

  ub4 dist;

  ub4 lochain;

  ub4 hopcnt; // initial by reference
  ub4 hopndx; // working rid-relative hop
  ub4 carriercnt;
  ub4 servicecnt;
  ub4 chaincnt; // chains in this route
  ub4 chainofs; // offset of list in routechains
  ub4 chainpos;
  ub4 hichainlen;
};

struct xferbase {
  ub4 fromport;
  ub4 toport;
  ub2 type;
  ub2 mintt;
};

// a carrier has one or more services on a route
// a service has a set of maps
// each map has entries for each go
// go contains one or more trips in a repeating pattern
// multiple maps are made when needed for duration difference or not fitting in map
struct sidbase {
  ub4 rsid;
  ub4 sid;
  ub4 cid;

  char name[256];
  ub4 namelen;

  bool valid;

  ub4 carrier;
  ub4 route;
  ub4 service;

  ub4 t0,t1;      // tt range in minutes std
  ub4 dow;

  char dowstr[8];

  ub4 lt0day,lt1day; // tt range in localtime days

  ub4 utcofs;     // minutes east from utc + 12h

  ub4 mapofs;     // day map
  ub4 maplen;     // in days
  ub4 daycnt;

  ub4 refcnt;
};

// main structure holding everything
struct networkbase {
  ub4 portcnt;
  ub4 subportcnt;
  ub4 hopcnt;
  ub4 sidcnt;
  ub4 ridcnt;
  ub4 tidcnt;
  ub4 xfercnt;
  ub4 agencycnt;

  ub4 rawchaincnt;
  ub4 chainhopcnt;
  ub4 timescnt;

  struct portbase *ports;
  struct subportbase *subports;
  struct hopbase *hops;
  struct sidbase *sids;
  struct routebase *routes;
  struct ridebase *rides;
  struct xferbase *xfers;
  struct chainbase *chains;

  ub8 *chainidxs;    // seq,ndx
  struct chainhopbase *chainhops;

  ub4 *routechains;
  ub4 *timesbase;
  ub8 *events; // srda.16 dtid.32 dur.32 t.32
  ub2 *evmaps;
  ub1 *sidmaps; // bit 7 enable bit 6 indst bit 5..0 rsid

  struct memblk portmem;
  struct memblk subportmem;
  struct memblk hopmem;
  struct memblk xfermem;
  struct memblk sidmem;
  struct memblk ridmem;
  struct memblk timesmem;
  struct memblk eventmem;

  ub4 latscale,lonscale;  // clicks per deg
  ub4 latrange[2];
  ub4 lonrange[2];

  ub4 t0,t1; // overall timebox in localtime + tz uncertainty
  ub4 tt0,tt1; // overall net date range

  ub4 utcofs12_def;
  ub4 feedstamp,feedlostamp;

// access

  ub4 *id2ports;         // [maxid]
  ub4 *subid2ports;      // [maxid]
  ub4 *rsid2sids;        // net, after omit empty
  ub4 *rsiddiag;
  ub4 *rrid2rid;
  ub4 *tid2rtid;
  ub4 *rsidmap;          // raw

  ub4 maxportid;
  ub4 maxsubportid;
  ub4 maxsid;

  ub4 timespanlimit;

  ub4 hitripid,hirrid,hichainlen;

  sb2 *faremaps;
};
typedef struct networkbase netbase;

enum Tentry { Tesid,Tetid,Tetripno,Tetdep,Tetarr,Terepiv,Terepstart,Terepend,Teseq,Tesdep,Tesarr,Tentries };

extern netbase *getnetbase(void);
extern int prepbasenet(void);

extern void ininetbase(void);
