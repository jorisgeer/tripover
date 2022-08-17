// net.h - main + derived network defines

/* structures and definitions for the main and derived network components
 * search-related defines are in src.h
 */

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2016 Joris van der Geer.
 */

/*
 a net consists of ports (aka stops) connected by hops (aka links,connections)
 routes are auxiliary

 connectivity is stored in sparse 2D port by port arrays for each of n stops aka transfers

 */

// number of connections stored locally
#define Nlocal 4

// max number of legs supported
#define Nleg (Nstop+1)

// longest precomputed trips
#define Netn 3

// max unique hops on a route for all trips
#define Chainlen 512

#define Faregrp 4

#if (Nstop < 12)
 #error "Nstop must be > 12"
#endif

// events: ref.1 | acc.15 | dtid.6 | dur.20 | rt.22
//         dtid 6 bits flight only
// sdeparr separate for ~1% with var deparr

// in minutes: typical max 7 days ~ 10k  14b = 11d
// +5b for 2-seconds  -> 21 for 24d
// dayno if ref
#define Durbits 14

// in minutes: typical timespan is few weeks: 3 * 7 * 1440 ~ 32k  18b = 177d
// +5b for 2 seconds -> 22 for 100d
#define Timbits 18

// 1440 * 90 / 5  = 25k  -> 5b for flights only
#define Dtidbits 16

// next pos at 4-hour,day,week intervals
#define Accbits 15

sassert(Durbits + Timbits + Dtidbits + Accbits < 64,"evbits <= 64") sassert_end

#define Timlim ((1U << Timbits) - 1)
#define Durlim ((1U << Durbits) - 1)
#define Dtidlim ((1U << Dtidbits) - 1)
#define Acclim ((1U << Accbits) - 1)

#define Durshift Timbits
#define Dtidshift (Timbits + Durbits)
#define Accshift (Timbits + Durbits + Dtidbits)

#define Acc1iv (4 * 60)
#define Acc2iv (24 * 60)
#define Acc3iv (24 * 60 * 7)

#define Acc1bits 5
#define Acc2bits 5
#define Acc3bits 5

sassert(Acc1bits + Acc2bits + Acc3bits <= Accbits,"acc123bits <= accbits") sassert_end

#define Acc1len (1U << Acc1bits)
#define Acc1lim ((1U << Acc1bits) - 1)
#define Acc2len (1U << Acc2bits)
#define Acc2lim ((1U << Acc2bits) - 1)
#define Acc3len (1U << Acc3bits)
#define Acc3lim ((1U << Acc3bits) - 1)

#define Acc1shift Accshift
#define Acc2shift (Accshift + Acc1bits)
#define Acc3shift (Accshift + Acc1bits + Acc2bits)

// base #cells per axis
#define Geogrid 256

// 640 m distance units
#define Gridshift 6

#define Nbrmask 0x1fffffff
#define Viabit (1U << 31)
#define Trip0bit (1U << 30)
#define Trip1bit (1U << 29)
#define Tripbits (3U << 29)

enum txkind { Unknown,Airint,Airdom,Rail,Bus,Ferry,Taxi,Walk,Kindcnt };
enum txbits { Airintbit=1,Airdombit=2,Railbit=4,Busbit=8,Ferrybit=16,Taxibit=32,Walkbit=64 };
#define Airbit (Airintbit|Airdombit)

enum carriers {
 XX,
 K3K, M4M, W9W, AA, AB, AC, AF, AM, AR, AS, AT, AX, AY, AZ,
 BA, BR,
 CA, CI, CM, CX, CZ,
 DL,
 EI, EK,
 FJ,
 GA, GK,
 HG,
 IB, IE, IS,
 JJ, JL, JQ,
 KA, KE, KL, KQ,
 LA, LH, LO, LX,
 ME, MF, MH, MS, MU,
 NF, NH, NZ,
 OK, OS, OU, OZ,
 PG, PX,
 QF, QR,
 RJ, RO,
 S7, SA, SB, SK, SN, SU, SV,
 TK, TL, TN, TP,
 UA, UL, UX,
 VN, VW,
 WP, WS,
 XL,
 Carriercnt
};

struct port {
  ub4 magic;
  ub4 id;      // index in net.ports
  ub4 cid;
  ub4 stopid;
  ub4 allid;

  char name[256];
  char intname[256];
  char iname[256];
  char prefix[64];
  ub4 namelen,intnamelen;
  ub4 prefixlen;

  ub4 gid;   // global port, index in gnet.ports

  ub4 lat,lon;
  double rlat,rlon;
  ub4 gridseq;
  ub4 gridlat,gridlon;
  ub8 sumreach;
  ub4 msbreach;

  ub4 subcnt,subofs,smapofs;

  ub4 nidcar,nidfoot;  // osm nearest nodes
  ub4 nidist;

  ub4 utcofs,dstonof;

  ub4 modes;  // mask of txbits

  bool valid;

  ub4 ndep,narr,nda;   // generic connectivity info
  ub4 nwsdep,nwldep;
  ub4 infconcnt,infiter;
  ub4 txreach[Nstop];

  ub8 con0ofs,con1ofs,con2ofs; // start offset for conofs per arr

  ub4 depofs[Netn],depcnt[Netn]; // [midcnt] list of n-stop outbounds
  ub4 arrofs[Netn],arrcnt[Netn]; // idem, inbounds
  ub4 viacnt[Netn]; // idem, via only

  ub2 tripstart,tripend; unused ?

  bool oneroute;
  bool loop;
  bool taxi;
  bool geo;
  ub4 onerid;

  ub4 deps[Nlocal];     // store small net locally
  ub4 arrs[Nlocal];
  ub4 drids[Nlocal];
  ub4 arids[Nlocal];
};

struct sport {
  ub4 id;
  ub4 stopid;
  ub4 cid;     // constant at net changes
  ub4 parent;

  char name[256];
  char intname[256];
  ub4 namelen,intnamelen;

  bool valid;

  ub4 ndep,narr;
  ub4 modes;

  ub4 lat,lon;
  double rlat,rlon;
  ub2 seq;
};

struct chainhop {
  ub4 hop;
  ub4 chain;
  ub4 tdep,tarr;
  ub4 midur;
  ub4 seq;
  ub4 srda;
};

struct chain {
  ub4 rrid,rid;
  ub4 rtid,dtid;
  ub4 tripno;
  ub4 hopcnt;
  ub4 rhopcnt;
  ub4 hopofs;
  ub4 rhopofs;
  ub8 code;
  ub1 uni;
};

struct timepat {
  ub4 utcofs;
  ub4 ht0,ht1; // min utc overall validity range

  ub4 gt0;
  ub4 t0,t1;   // relative to above actual event range
  ub4 lodur,hidur,midur,avgdur,duracc;
  ub4 evofs;   // offset in net.events
};

struct hop {
  ub4 magic;
  ub4 id;

  char name[128];
  ub4 namelen;

  ub2 reserve;
  ub2 fare;
  ub2 varsda;
  ub2 srdep,srarr;

  enum txkind kind;
  enum carriers carrier;

  ub4 dep,arr;    // within part
  ub4 gdep,garr;  // global

  ub4 rrid,rid;
  ub4 rhop;  // relative within rid
  ub4 grp;  // chain group for split routes

  ub2 tripstart,tripend;

  ub4 evcnt;

  struct timepat tp;
  int overtake;

  ub4 dist;
};

struct chop {
  ub4 rid;
  ub4 aid;
  ub4 rhop;  // relative within rid

  ub4 hop1,hop2; // base hops

  ub4 choplo,chophi,chopcnt; // if base: hop range of compounds derived from this
  ub4 evcnt;

  ub1 reserve;
  ub1 hasfrq;
  ub1 haveacc;
  ub2 net0,net1;

  ub2 fare;
  ub2 overtake;
  ub2 varsda;

  ub2 tripstart,tripend;
  ub2 ckind;
  ub2 ctype;

  ub2 srdep,srarr;

  enum txkind kind;
  enum carriers carrier;

  ub4 dep,arr;

  ub8 evofs;
  ub8 sdaofs;
  ub4 dayofs;

  ub4 lodur,hidur;
  // ub4 typdt;
  // ub4 avgdt;
  // ub4 hidt;
  // ub4 avgperhr,cnthr;

  ub4 daypos;
  ub4 daycnt;
  ub4 daylolen,dayhilen;  // todo thop

  ub4 t0,t1;  // absolute time range
  ub4 dist;
};

enum Croutes { Croute_walk, Croute_taxi, Croute_cnt };

struct route {
  ub4 magic;
  ub4 id;
  ub4 rid;

  char name[256];
  ub4 namelen;

  ub2 reserve;
  ub2 fare;

  char ckind;

  enum txkind kind;
  ub4 aid;

  int loop;

  ub4 startport;

  ub4 rrid;
  ub4 hopcnt;
  ub4 hichainlen;
  ub4 hops[Chainlen];  // hops for <rid,dep,arr> to hop lookup
  ub4 hop2pos;

  ub4 lochop,chopcnt;  // first and count of chops generated for it

  ub4 lohop,hihop;     // first and last in sorted hops
  ub4 lochain,hichain; // first and last in sorted chains

  ub4 chainofs;        // in dtid lookup[chaincnt]. not needed if sorted
  ub4 chaincnt;

  ub2 acc1tab[Acc1len];
  ub2 acc2tab[Acc2len];
  ub2 acc3tab[Acc3len];
  ub4 acc1len,acc2len,acc3len;
};

struct xfer {
  ub4 fromport;
  ub4 toport;
  ub2 type;
  ub2 mintt;
};

// a carrier has one or more services on a route
// a service has a set of maps
// each map has entries for each go
struct sidtable {
  ub4 magic;
  ub4 id;
  ub4 sid;

  char name[128];
  ub4 namelen;

  ub4 t0,t1;
};

// holds all
struct network {
  ub4 portcnt,vportcnt,sportcnt;
  ub4 hopcnt,chopcnt,thopcnt,whopcnt;

  ub4 sidcnt;
  ub4 chaincnt;
  ub4 ridcnt,pridcnt;
  ub4 xfercnt;
  ub4 agencycnt;

  ub4 chainhopcnt;

  struct port *ports;
  struct sport *sports;
  struct hop *hops;
  struct chop *chops;  // [whopcnt]
  struct chain *chains;

  struct route *routes;
  struct sidtable *sids;
  struct xfer *xfers;

  struct chainhop *chainhops;  // points to gnet

// timetables: pointer to basenet
  block *eventmem;
  ub8 *events;       // [hopcnt * 2] <time,dur+tid> tuples

  block cevmem;
  ub8 *cevents;    // [chopcnt * evcnt] acc,dtid,dur,rt

  // variable sub deparr
  block sdamem;

  // ub4 *cevents2;     // todo unused

  ub2 *evsrdas;    // [chopcnt * evcnt] srdep,srarr

  ub8 *reltab;     // [nzdaycnt] evofs for each referred day

  ub8 *daymap;     // = reltab ?

  //ub4 *sevents;      // [samplecnt * chopcnt] dur+time
  //ub4 *sevcnts;      // [chopcnt]
  ub4 t0,t1;         // overall period
  ub4 tt0,tt1;       // overall net date range

// fares: idem
  ub2 *fareposbase;
  ub8 fareposcnt;
  block faremem;
  ub4 *ridhopbase;

  ub4 *fhopofs;     // [chopcnt] offsets into faremem

// access
  ub4 *portsbyhop; // [whopcnt * 2] <dep,arr>

  ub4 *hopdist;    // [whopcnt]

  ub4 *routechains; // [tidcnt]

  ub1 *hopmodes;   // [whopcnt] tx modes

// connection matrices.
  ub4 histop;      // highest n-stop connections inited
  ub4 maxstop;     // highest n-stop connections to be inited
  ub4 walklimit;   // in geo's
  ub4 sumwalklimit;
  ub4 walkspeed;   // geo's per hour
  ub4 net1walklimit,net2walklimit;

  ub4 sparsethres;

  ub4 latscale,lonscale;

  ub4 hirrid;

  ub4 hinda;

  ub4 *tid2rtid;   // [chaincnt]
  ub4 hichainlen;

  size_t needconn;    // final required any-stop connectivity
  size_t haveconn[Nstop];

  iadrbase noxfer;

// idem for each of n-stop...
  iadrbase concnt0;
  iadrbase concnt1;
  iadrbase concnt2;

  iadrbase conipos;    // temp

  iadrbase lst1items,lst2items;

  iadrbase conofs0; // [port2 ub4] relative triplet offset in conlst per pair
  iadrbase conofs1; // [port2 ub4]
  iadrbase conofs2; // [port2 ub4]

  iadrbase durlims0;

  iadrbase distlims;

  iadrbase hoptx;

  block conlst0;  // [lstlen * nleg] direct ub4 hop
  block conlst1;  // [lstlen * nleg] indir ub2 index
  block conlst2;  // [lstlen * nleg] indir ub2 index

  size_t lstlen[Nstop];
  size_t pairs[Nstop];

  ub1 *modes[Nstop];     // [lstlen]

  ub4 *portdst[Nstop];  // [portcnt] #destinations per port

  ub4 disthis[Nstop];   // highest values at end of nstop
  ub4 durhis[Nstop];

  ub4 *deplst[Nstop];
  ub4 *arrlst[Nstop];     // [pairs] n-stop out- and inbounds
  ub4 *depdurlst[Nstop];  // [pairs] n-stop out- and inbound durs
  ub4 *arrdurlst[Nstop];  // [pairs] n-stop out- and inbound durs

  ub2 *seqdist;     // coarse geo dist
  ub1 *seqlotx;     // coarse low tx
  ub4 seqdlen;

  ub4 gridscale;

  bool havelotx;

  ub1 *submaps;     // [cum subcnt^2] subport dist maps

  ub4 bbox[10];    // lat/lon bounding box

  ub1 *shares; // [Carriercnt * Carriercnt]

// geo lookup
  ub4 *latsort,*lonsort;
  ub4 *latxsort,*lonxsort;
  ub4 *latsortidx,*lonsortidx;
  ub4 *latxsortidx,*lonxsortidx;

  enum carriers *carriercodes; // [64k]

  void *vosm;  // openstreetmap net
  ub4 nidcnt;

// prep
  ub2 *chainrhops;
  block ridhopmem;
  ub4 *rrid2rid;   // [hirrid+1]
  ub4 feedstamp,feedlostamp;
};
typedef struct network lnet;

typedef struct network gnet; // leftover from partitioning

#if 0
struct gnetwork {
  ub4 portcnt,sportcnt,zportcnt;
  ub4 hopcnt,chopcnt,zhopcnt;
  ub4 sidcnt;
  ub4 ridcnt;
  ub4 xfercnt;
  ub4 agencycnt;
  ub4 chaincnt;
  ub4 chainhopcnt;

  struct port *ports;
  struct sport *sports;
  struct hop *hops;
  struct chop *chops;
  struct sidtable *sids;
  struct chain *chains;
  struct route *routes;
  struct xfer *xfers;

  ub4 *portsbyhop; // [hopcnt * 2] <dep,arr>

  ub4 *hopdist;    // [chopcnt] distance
  ub4 *hopdur;     // [chopcnt] average / typical duration
  ub4 *hopcdur;     // [chopcnt] compound constant duration
  ub4 *choporg;    // [chopcnt * 2] <first,last>

  ub4 partcnt;

// timetables: pointer to basenet
  block *eventmem;
  block *evmapmem;
  ub8 *events;
  ub2 *evmaps;
  ub4 t0,t1;  // overall period
  ub4 tt0,tt1; // overall net date range

  block covhrmem,covdymem;  // event coverage maps
  ub1 *covhr;      // [chopcnt * (t1 - t0) / 60] hourly event counts
  ub2 *covdy;      // [chopcnt * (t1 - t0) / 1440] daily event counts
  ub8 rnghr;
  ub4 rngdy;

  ub8 cevcnt;
  block cevmem;
  ub8 *cevents;    // [chopcnt * evcnt] t,dur,dtid,acc

  // variable sub deparr
  block sdamem;

  block srarrmem;
  ub1 *evsrarrs;    // [chopcnt * evcnt] srarr

// fares and availability
  block faremem;
  ub2 *fareposbase;
  ub8 fareposcnt;
  ub4 *fhopofs;     // [chopcnt] offsets into faremem

  struct chainhop *chainhops;
  ub2 *chainrhops;
  ub4 *routechains; // [tidcnt]

  ub4 *tid2rtid;   // [chaincnt]
  ub4 *rrid2rid;   // [hirrid+1]
  struct memblk ridhopmem;
  ub4 *ridhopbase;

  ub1 *submaps;     // [cum subcnt^2] subport dist maps

  ub4 bbox[10];    // lat/lon bounding box

  ub4 histop;     // highest n-stop connections inited
  ub4 walklimit;
  ub4 sumwalklimit;
  ub4 walkspeed;  // geo's per hour
  ub4 sparsethres;

  ub4 feedstamp,feedlostamp;

  ub4 latscale,lonscale;

  enum carriers *carriercodes; // [64k]
  ub1 *shares; // [Carriercnt * Carriercnt]

  // geo lookup
  ub4 *latxsort,*lonxsort;
  ub4 *latsort,*lonsort;
  ub4 *latxsortidx,*lonxsortidx;
  ub4 *latsortidx,*lonsortidx;

  ub4 hirrid;
  ub4 hichainlen;
};
typedef struct gnetwork gnet;
#endif

#define triptoports(net,trip,triplen,ports) triptoports_fln(FLN,(net),(trip),(triplen),(ports))

#define getmintt(tts,depkind,arrkind) (tts)[((depkind) << 4) | (arrkind)]

extern int mknet(ub4 maxstop,struct network *net);
extern struct network *getnet(void);
extern int triptoports_fln(ub4 fln,struct network *net,ub4 *trip,ub4 triplen,ub4 *ports);

#define checktrip(net,legs,nleg,dep,arr,dist) checktrip_fln((net),(legs),(nleg),(dep),(arr),(dist),FLN)
#define checktrip3(net,legs,nleg,dep,arr,via,dist) checktrip3_fln((net),(legs),(nleg),(dep),(arr),(via),(dist),FLN)
extern int checktrip_fln(struct network *net,ub4 *legs,ub4 nleg,ub4 dep,ub4 arr,ub4 dist,ub4 fln);
extern int checktrip3_fln(struct network *net,ub4 *legs,ub4 nleg,ub4 dep,ub4 arr,ub4 via,ub4 dist,ub4 fln);

extern ub4 fgeodist(struct port *pdep,struct port *parr,int silent);
extern int geocode(ub4 ilat,ub4 ilon,ub4 scale,ub1 txmask,struct myfile *rep);
extern ub4 geocode2(ub4 ilat,ub4 ilon,ub4 scale,ub1 txmask,struct myfile *rep);

// extern int showconn(struct network *net);
extern void mkmintt(ub4 *tts,ub4 depmask,ub4 arrmask,ub4 val);
// extern ub4 getmintt(ub4 *tts,ub4 depkind,ub4 arrkind);
extern const char *modename(enum txkind mode);
extern char hoptype(struct network *net,ub4 hop);

#define hopmsg(lvl,code,hop,fmt,...) hopmsgfln(FLN,(lvl),(code),(hop),(fmt),__VA_ARGS__)
extern int hopmsgfln(ub4 fln,ub4 lvl,ub4 code,ub4 hop,const char *fmt,...) __attribute__ ((format (printf,5,6)));

extern void ininet(void);
