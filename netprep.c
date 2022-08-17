// netprep.c - prepare net from base

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2016 Joris van der Geer.
 */

/*
  copy work lists from i/o based base lists
 */

#include <string.h>
#include <stdlib.h>

#include "base.h"
#include "cfg.h"
#include "mem.h"
#include "math.h"

static ub4 msgfile;
#include "msg.h"

#include "iadr.h"
#include "util.h"
#include "netbase.h"
#include "netio.h"
#include "net.h"
#include "netprep.h"

void ininetprep(void)
{
  msgfile = setmsgfile(__FILE__);
  iniassert();
}

static enum txkind bkind2kind(enum txbkind b,char *p)
{
  *p = 'X';
  switch(b) {
  case Unknownb: *p = 'X'; return Unknown;
  case Airintb: *p = 'A'; return Airint;
  case Airdomb: *p = 'a'; return Airdom;
  case Railb: *p = 'r'; return Rail;
  case Busb: *p = 'b'; return Bus;
  case Ferryb: *p = 'f'; return Ferry;
  case Taxib: *p = 't'; return Taxi;
  case Walkb: *p = 'w'; return Walk;
  case Kindcntb: *p = 'X'; return Kindcnt;
  }
  return Unknown;
}

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wmissing-field-initializers"
static struct airlinedef {
  char code[2];
  enum carriers carrier;
  enum carriers shares[64];
  const char *name;
} airlines[] = {
 { "3K", K3K, { K3K }, "Jetstar Asia" },
 { "4M", M4M, { M4M }, "Aero 2000" },
 { "9W", W9W, { W9W }, "Jet Airways" },
 { "AA", AA, { AA,AB,AY,BA,CX,IB,JJ,JL,LA,MH,QF,RJ,S7,UL }, "American Airlines" },
 { "AB", AB, { AA,AB,AY,BA,CX,IB,JJ,JL,LA,MH,QF,RJ,S7,UL }, "Air Berlin" },
 { "AC", AC, { AC }, "Air Canada" },
 { "AF", AF, { AF,AM,AR,AZ,CI,CZ,DL,GA,KE,KL,KQ,ME,MF,MU,OK,RO,SU,SV,UX,VN }, "Air France" },
 { "AM", AM, { AF,AM,AR,AZ,CI,CZ,DL,GA,KE,KL,KQ,ME,MF,MU,OK,RO,SU,SV,UX,VN }, "Aeroméxico" },
 { "AR", AR, { AF,AM,AR,AZ,CI,CZ,DL,GA,KE,KL,KQ,ME,MF,MU,OK,RO,SU,SV,UX,VN }, "Aerolíneas Argentinas" },
 { "AS", AS, { AS }, "Alaska Airlines" },
 { "AX", AX, { AX }, "Trans States Airlines" },
 { "AY", AY, { AA,AB,AY,BA,CX,IB,JJ,JL,LA,MH,QF,RJ,S7,UL }, "Finnair" },
 { "AZ", AZ, { AF,AM,AR,AZ,CI,CZ,DL,GA,KE,KL,KQ,ME,MF,MU,OK,RO,SU,SV,UX,VN }, "Alitalia" },
 { "BA", BA, { AA,AB,AY,BA,CX,IB,JJ,JL,LA,MH,QF,RJ,S7,UL }, "British Airways" },
 { "BR", BR, { BR }, "EVA Airways" },
 { "CA", CA, { CA }, "Air China" },
 { "CI", CI, { AF,AM,AR,AZ,CI,CZ,DL,GA,KE,KL,KQ,ME,MF,MU,OK,RO,SU,SV,UX,VN }, "China Airlines" },
 { "CM", CM, { CM }, "Compania Panamena de Aviacion" },
 { "CX", CX, { AA,AB,AY,BA,CX,IB,JJ,JL,LA,MH,QF,RJ,S7,UL }, "Cathay Pacific" },
 { "CZ", CZ, { AF,AM,AR,AZ,CI,CZ,DL,GA,KE,KL,KQ,ME,MF,MU,OK,RO,SU,SV,UX,VN }, "China Southern Airlines" },
 { "DL", DL, { AF,AM,AR,AZ,CI,CZ,DL,GA,KE,KL,KQ,ME,MF,MU,OK,RO,SU,SV,UX,VN }, "Delta Airlines" },
 { "EI", EI, { EI }, "Aer Lingus" },
 { "EK", EK, { EK }, "Emirates" },
 { "FJ", FJ, { FJ }, "Fiji Airways" },
 { "GA", GA, { AF,AM,AR,AZ,CI,CZ,DL,GA,KE,KL,KQ,ME,MF,MU,OK,RO,SU,SV,UX,VN }, "Garuda Indonesia" },
 { "GK", GK, { GK }, "Jetstar Japan" },
 { "HG", HG, { HG }, "NIKI Luftfahrt" },
 { "IB", IB, { AA,AB,AY,BA,CX,IB,JJ,JL,LA,MH,QF,RJ,S7,UL }, "Iberia Lineas Aereas" },
 { "IE", IE, { IE }, "Solomon Airlines" },
 { "IS", IS, { IS }, "" },
 { "JJ", JJ, { AA,AB,AY,BA,CX,IB,JJ,JL,LA,MH,QF,RJ,S7,UL }, "TAM Linhas Aereas" },
 { "JL", JL, { AA,AB,AY,BA,CX,IB,JJ,JL,LA,MH,QF,RJ,S7,UL }, "Japan Airlines" },
 { "JQ", JQ, { JQ }, "Jetstar Airways" },
 { "KA", KA, { KA }, "Dragon Airlines " },
 { "KE", KE, { AF,AM,AR,AZ,CI,CZ,DL,GA,KE,KL,KQ,ME,MF,MU,OK,RO,SU,SV,UX,VN }, "Korean Air Lines" },
 { "KL", KL, { AF,AM,AR,AZ,CI,CZ,DL,GA,KE,KL,KQ,ME,MF,MU,OK,RO,SU,SV,UX,VN }, "KLM Royal Dutch Airlines" },
 { "KQ", KQ, { AF,AM,AR,AZ,CI,CZ,DL,GA,KE,KL,KQ,ME,MF,MU,OK,RO,SU,SV,UX,VN }, "Kenya Airways" },
 { "LA", LA, { AA,AB,AY,BA,CX,IB,JJ,JL,LA,MH,QF,RJ,S7,UL }, "LAN Airlines" },
 { "LH", LH, { LH }, "Lufthansa" },
 { "LO", LO, { LO }, "LOT - Polish Airlines" },
 { "LX", LX, { LX }, "SWISS International Air Lines" },
 { "ME", ME, { AF,AM,AR,AZ,CI,CZ,DL,GA,KE,KL,KQ,ME,MF,MU,OK,RO,SU,SV,UX,VN }, "AirLiban Middle East Airlines" },
 { "MF", MF, { AF,AM,AR,AZ,CI,CZ,DL,GA,KE,KL,KQ,ME,MF,MU,OK,RO,SU,SV,UX,VN }, "Xiamen Airlines" },
 { "MH", MH, { AA,AB,AY,BA,CX,IB,JJ,JL,LA,MH,QF,RJ,S7,UL }, "Malaysia Airlines" },
 { "MS", MS, { MS }, "Egyptair" },
 { "MU", MU, { AF,AM,AR,AZ,CI,CZ,DL,GA,KE,KL,KQ,ME,MF,MU,OK,RO,SU,SV,UX,VN }, "China Eastern Airlines" },
 { "NF", NF, { NF }, "Air Vanuatu" },
 { "NH", NH, { NH }, "All Nippon Airways" },
 { "NZ", NZ, { NZ }, "Air New Zealand" },
 { "OK", OK, { AF,AM,AR,AZ,CI,CZ,DL,GA,KE,KL,KQ,ME,MF,MU,OK,RO,SU,SV,UX,VN }, "Czech Airlines" },
 { "OS", OS, { OS }, "Austrian Airlines" },
 { "OU", OU, { OU }, "Croatia Airlines" },
 { "OZ", OZ, { OZ }, "Asiana Airlines" },
 { "PG", PG, { PG }, "Bangkok Airways" },
 { "PX", PX, { PX }, "Air Niugini" },
 { "QF", QF, { AA,AB,AY,BA,CX,IB,JJ,JL,LA,MH,QF,RJ,S7,UL }, "Qantas Airways" },
 { "QR", QR, { QR }, "Qatar Airways" },
 { "RJ", RJ, { AA,AB,AY,BA,CX,IB,JJ,JL,LA,MH,QF,RJ,S7,UL }, "Royal Jordanian" },
 { "RO", RO, { AF,AM,AR,AZ,CI,CZ,DL,GA,KE,KL,KQ,ME,MF,MU,OK,RO,SU,SV,UX,VN }, "TAROM" },
 { "S7", S7, { AA,AB,AY,BA,CX,IB,JJ,JL,LA,MH,QF,RJ,S7,UL }, "Siberia Airlines" },
 { "SA", SA, { SA }, "South African Airways" },
 { "SB", SB, { SB }, "Air Caledonie" },
 { "SK", SK, { SK }, "SAS Scandinavian Airlines" },
 { "SN", SN, { SN }, "Brussels Airlines" },
 { "SU", SU, { AF,AM,AR,AZ,CI,CZ,DL,GA,KE,KL,KQ,ME,MF,MU,OK,RO,SU,SV,UX,VN }, "Aeroflot" },
 { "SV", SV, { AF,AM,AR,AZ,CI,CZ,DL,GA,KE,KL,KQ,ME,MF,MU,OK,RO,SU,SV,UX,VN }, "Saudi Arabian Airlines" },
 { "TK", TK, { TK }, "Turkish Airlines" },
 { "TL", TL, { TL }, "Airnorth" },
 { "TN", TN, { TN }, "Air Tahiti" },
 { "TP", TP, { TP }, "TAP Portugal" },
 { "UA", UA, { UA }, "United Airlines" },
 { "UL", UL, { AA,AB,AY,BA,CX,IB,JJ,JL,LA,MH,QF,RJ,S7,UL }, "SriLankan Airlines" },
 { "UX", UX, { AF,AM,AR,AZ,CI,CZ,DL,GA,KE,KL,KQ,ME,MF,MU,OK,RO,SU,SV,UX,VN }, "Air Europe Lineas Aereas" },
 { "VN", VN, { AF,AM,AR,AZ,CI,CZ,DL,GA,KE,KL,KQ,ME,MF,MU,OK,RO,SU,SV,UX,VN }, "Vietnam Airlines" },
 { "VW", VW, { VW }, "Transportes Aeromar" },
 { "WP", WP, { WP }, "Hawaii Island Air" },
 { "WS", WS, { WS }, "WestJet" },
 { "XL", XL, { XL }, "Lan Ecuador" },
 { "", XX }
};
#pragma GCC diagnostic pop

static int prepair(gnet *net)
{
  ub4 code,linendx = 0;
  ub4 share2,carrier2 = Carriercnt * Carriercnt;
  struct airlinedef *dp = airlines;
  enum carriers carrier,*csp,*ap = alloc0(1 << 16,enum carriers,0xff);
  ub1 ca1,ca2;
  ub1 *shares = alloc0(carrier2,ub1,0);

  sassert(Carriercnt < 256,"carriers < 256");
  while (dp->carrier && dp->carrier != Carriercnt) {
    ca1 = dp->code[0]; ca2 = dp->code[1];
    error_z_cc(ca1,"entry %u %s",linendx,dp->name);
    error_z_cc(ca2,"entry %u %s",linendx,dp->name);
    code = (ub4)ca1 << 8 | ca2;
    error_ge(code,hi16);
    carrier = ap[code] = dp->carrier;
    csp = dp->shares;
    share2 = (ub4)carrier * Carriercnt;
    while (csp < dp->shares + Elemcnt(dp->shares) && *csp) shares[share2 + *csp++] = 1;
    linendx++;
    dp++;
  }
  net->carriercodes = ap;
  net->shares = shares;
  return 0;
}

static int prepgeo(gnet *net)
{
  struct port *pdep,*ports = net->ports;
  struct sport *sp,*sports = net->sports;
  ub4 portcnt = net->portcnt;
  ub4 sportcnt = net->sportcnt;
  ub4 xportcnt = portcnt + sportcnt;
  ub4 dep,idx;
  ub4 lat,lon;

  // sports after ports
  ub8 xlat,*latx8sort = talloc(xportcnt,ub8,0,"geo xlat",xportcnt);
  ub8 xlon,*lonx8sort = talloc(xportcnt,ub8,0,"geo xlon",xportcnt);
  ub8 *lat8sort = talloc(portcnt,ub8,0,"geo lat",portcnt);
  ub8 *lon8sort = talloc(portcnt,ub8,0,"geo lon",portcnt);

  // ports+sports for geocode
  ub4 *latxsort = alloc(xportcnt,ub4,0,"geo xlat",xportcnt);
  ub4 *lonxsort = alloc(xportcnt,ub4,0,"geo xlon",xportcnt);
  ub4 *latxsortidx = alloc(xportcnt,ub4,0,"geo xlatidx",xportcnt);
  ub4 *lonxsortidx = alloc(xportcnt,ub4,0,"geo xlonidx",xportcnt);

  // ports only for walklinks
  ub4 *latsort = alloc(portcnt,ub4,0,"geo lat",portcnt);
  ub4 *lonsort = alloc(portcnt,ub4,0,"geo lon",portcnt);
  ub4 *latsortidx = alloc(portcnt,ub4,0,"geo latidx",portcnt);
  ub4 *lonsortidx = alloc(portcnt,ub4,0,"geo lonidx",portcnt);

  // prepare bsearch for geo lookup
  for (dep = 0; dep < portcnt; dep++) {
    pdep = ports + dep;
    lat = pdep->lat; lon = pdep->lon;
    xlat = (ub8)lat << 32 | dep;
    xlon = (ub8)lon << 32 | dep;
    latx8sort[dep] = xlat;
    lonx8sort[dep] = xlon;
    lat8sort[dep] = xlat;
    lon8sort[dep] = xlon;
  }
  for (dep = portcnt; dep < xportcnt; dep++) {
    sp = sports + dep - portcnt;
    lat = sp->lat; lon = sp->lon;
    xlat = (ub8)lat << 32 | dep;
    xlon = (ub8)lon << 32 | dep;
    latx8sort[dep] = xlat;
    lonx8sort[dep] = xlon;
  }
  sort8(latx8sort,xportcnt,FLN,"latsort");
  sort8(lonx8sort,xportcnt,FLN,"lonsort");

  // separate sorted list into coord and index
  for (idx = 0; idx < xportcnt; idx++) {
    xlat = latx8sort[idx];
    xlon = lonx8sort[idx];
    lat = (ub4)(xlat >> 32);
    lon = (ub4)(xlon >> 32);
    dep = (ub4)xlat & hi32;
    latxsort[idx] = lat;
    latxsortidx[idx] = dep;
    dep = (ub4)xlon & hi32;
    lonxsort[idx] = lon;
    lonxsortidx[idx] = dep;
  }

  // idem for planning ports only
  sort8(lat8sort,portcnt,FLN,"latsort");
  sort8(lon8sort,portcnt,FLN,"lonsort");

  // separate sorted list into coord and index
  for (idx = 0; idx < portcnt; idx++) {
    xlat = lat8sort[idx];
    xlon = lon8sort[idx];
    lat = (ub4)(xlat >> 32);
    lon = (ub4)(xlon >> 32);
    dep = (ub4)xlat & hi32;
    latsort[idx] = lat;
    latsortidx[idx] = dep;
    dep = (ub4)xlon & hi32;
    lonsort[idx] = lon;
    lonsortidx[idx] = dep;
  }

  net->latxsort = latxsort;
  net->lonxsort = lonxsort;
  net->latxsortidx = latxsortidx;
  net->lonxsortidx = lonxsortidx;
  net->latsort = latsort;
  net->lonsort = lonsort;
  net->latsortidx = latsortidx;
  net->lonsortidx = lonsortidx;
  return 0;
}

int prepnet(netbase *basenet,struct network *glnet)
{
  struct portbase *bports,*bpp,*bpdep,*bparr;
  struct subportbase *bsports,*bspp;
  struct hopbase *bhops,*bhp;
  struct sidbase *bsids,*bsp;
  struct chainbase *bchains,*bcp;
  struct routebase *broutes,*brp;
  struct xferbase *bxfers,*bxp;

  ub8 *bchip,*bchainidxs;
  struct chainhopbase *bchp,*bchainhops;

  struct port *ports,*pdep,*parr,*pp;
  struct sport *sports,*spp,*spp2;
  struct hop *hops,*hp,*hp2;
  struct sidtable *sids,*sp;
  struct chain *chains,*cp;
  struct route *routes,*rp;
  struct xfer *xp,*xfers = NULL;
  struct timepatbase *btp;
  struct timepat *tp;

  sassert(sizeof(ports->name) == sizeof(bports->name),"ports name len mismatch");
  sassert(sizeof(ports->prefix) == sizeof(bports->prefix),"ports prefix len mismatch");
  sassert(sizeof(sports->name) == sizeof(bsports->name),"ports name len mismatch");

  sassert(sizeof(routes->name) == sizeof(broutes->name),"route name len mismatch");

  ub4 bportcnt,portcnt;
  ub4 bsportcnt,sportcnt;
  ub4 bhopcnt,hopcnt;
  ub4 dep,arr;
  ub4 bsidcnt,sidcnt,bchaincnt,chaincnt,chainhopcnt;
  ub4 bridcnt,ridcnt;
  ub4 bxfercnt,xfercnt;
  ub4 nlen,inlen,cnt,acnt,dcnt,sid,rid,brid,rrid,pos;
  ub4 scnt,smapofs = 0,cumscnt = 0;

  enum txbkind bkind;
  ub4 hop,port,sport,sport2,chain;

  ub4 hirrid = basenet->hirrid;
  ub4 *rrid2rid = alloc(hirrid+1,ub4,0,"rrid2rid",0);

  bhopcnt = basenet->hopcnt;
  bportcnt = basenet->portcnt;
  bsportcnt = basenet->subportcnt;
  bsidcnt = basenet->sidcnt;
  bridcnt = basenet->ridcnt;
  bxfercnt = xfercnt = basenet->xfercnt;
  bchaincnt = basenet->rawchaincnt;
  if (bportcnt == 0 || bhopcnt == 0) return error(0,"prepnet: %u ports, %u hops",bportcnt,bhopcnt);

  prepair(glnet);

  // filter but leave placeholder in gnet to make refs match
  ports = alloc(bportcnt,struct port,0,"ports",bportcnt);
  portcnt = 0;
  bports = basenet->ports;
  for (port = 0; port < bportcnt; port++) {
    bpp = bports + port;
    pp = ports + port;
    nlen = bpp->prefixlen;
    if (nlen) memcpy(pp->prefix,bpp->prefix,nlen);
    pp->prefixlen = nlen;

    nlen = bpp->namelen;
    inlen = bpp->intnamelen;
    if (nlen) memcpy(pp->name,bpp->name,nlen);
    else warn(0,"port %u has no name",port);
    pp->namelen = nlen;
    if (inlen) memcpy(pp->intname,bpp->intname,inlen);
    else warn(0,"port %u has no int name",port);
    pp->intnamelen = inlen;

    // info(0,"port %u name '%s' iname '%s'",port,pp->name,pp->intname);
    pos = fmtstring(pp->iname,"%s %.*s %s",pp->prefix,truncutf8(pp->name,64),pp->name,strcmp(bpp->name,bpp->intname) ? bpp->intname : "");
    if (sizeof(pp->iname) - pos < 16) return error(0,"pfx %s name %s int %s",pp->prefix,pp->name,bpp->intname);

    if (bpp->geo == 0 && bpp->ndep == 0 && bpp->narr == 0) {
      warn(0,"skip unconnected port %u %s %s",port,bpp->prefix,bpp->name);
      continue;
    }

    // new ndep,narr filled lateron
    pp->valid = 1;
    pp->id = pp->allid = pp->gid = portcnt;
    pp->cid = bpp->cid;
    pp->stopid = bpp->stopid;
    pp->lat = bpp->lat;
    pp->lon = bpp->lon;
    pp->rlat = bpp->rlat;
    pp->rlon = bpp->rlon;
    if (bpp->air) pp->modes |= Airbit;
    if (bpp->rail) pp->modes |= Railbit;
    if (bpp->bus) pp->modes |= Busbit;
    if (bpp->ferry) pp->modes |= Ferrybit;
    if (bpp->taxi) pp->modes |= Taxibit;
    pp->utcofs = bpp->utcofs;
    pp->dstonof = bpp->dstonof;
    pp->geo = bpp->geo;
    scnt = bpp->subcnt;
    error_gt(cumscnt,1 << 30,port);
    cumscnt += scnt * scnt;
    pp->subcnt = scnt;
    pp->subofs = bpp->subofs;
    portcnt++;
  }
  info(0,"%u from %u ports",portcnt,bportcnt);
  // error_ne(portcnt,bportcnt);
  portcnt = bportcnt;

  sports = alloc(bsportcnt,struct sport,0,"sports",bsportcnt);
  sportcnt = 0;
  bsports = basenet->subports;
  for (sport = 0; sport < bsportcnt; sport++) {
    bspp = bsports + sport;
    spp = sports + sport;

    nlen = bspp->namelen;
    inlen = bspp->intnamelen;
    if (nlen) memcpy(spp->name,bspp->name,nlen);
    else info(0,"sport %u has no name",sport);
    spp->namelen = nlen;
    if (inlen) memcpy(spp->intname,bspp->intname,inlen);
    else info(0,"sport %u has no int name",sport);
    spp->intnamelen = inlen;

    if (bspp->ndep == 0 && bspp->narr == 0) {
      vrb0(Notty,"unconnected subport %u %s",sport,bspp->name);
    }

    spp->valid = 1;
    spp->id = sportcnt;
    spp->cid = bspp->cid;
    spp->stopid = bspp->stopid;
    spp->parent = bspp->parent;
    spp->lat = bspp->lat;
    error_z(spp->lat,sport);
    spp->lon = bspp->lon;
    spp->rlat = bspp->rlat;
    spp->rlon = bspp->rlon;
    if (bspp->air) spp->modes |= Airbit;
    if (bspp->rail) spp->modes |= Railbit;
    if (bspp->bus) spp->modes |= Busbit;
    if (bspp->ferry) spp->modes |= Ferrybit;
    if (bspp->taxi) spp->modes |= Taxibit;
    spp->seq = bspp->seq;
    sportcnt++;
  }
  info(0,"%u from %u sports",sportcnt,bsportcnt);
  error_ne(sportcnt,bsportcnt);
  sportcnt = bsportcnt;

  // prepare walk durations
  ub4 walkspeed = m2geo(globs.walkspeed); // geo's per hour
  if (walkspeed == 0) {
    warn(0,"walkspeed %u -> %u set to 1",globs.walkspeed,walkspeed);
    walkspeed = 1;
  }
  glnet->walkspeed = walkspeed;

  double fdist,srdur,fwalkspeed = walkspeed;

  for (port = 0; port < portcnt; port++) {
    pp = ports + port;
    scnt = pp->subcnt;
    if (scnt == 0) continue;
    pp->smapofs = smapofs;
    smapofs += scnt * scnt;
  }
  ub1 *smp,*smaps = glnet->submaps = alloc(cumscnt,ub1,0,"port submap",cumscnt);
  ub8 smapcnt = 0;

  for (port = 0; port < portcnt; port++) {
    pp = ports + port;
    scnt = pp->subcnt;
    if (scnt == 0) continue;
    smp = smaps + pp->smapofs;
    for (sport = 0; sport < scnt; sport++) {
      spp = sports + pp->subofs + sport;
      for (sport2 = 0; sport2 < scnt; sport2++) {
        if (sport == sport2) continue;
        spp2 = sports + pp->subofs + sport2;
        if (spp->lat == spp2->lat && spp->lon == spp2->lon) continue;
        fdist = geodist(spp->rlat,spp->rlon,spp2->rlat,spp2->rlon,spp->name);
        srdur = (fdist * 60) / fwalkspeed;
//        srdur = max(srdur,1);
        infocc(srdur > 4,Notty|Iter|0,"port %u sub %u-%u dist %f dur %f %s %s-%s",port,sport,sport2,fdist,srdur,pp->name,spp->name,spp2->name);
        smp[spp->seq * scnt + spp2->seq] = (ub1)(srdur + 0.5);
        smapcnt++;
      }
    }
  }
  info(0,"\ah%lu port subentries",smapcnt);

  // sids
  sidcnt = bsidcnt;
  sids = alloc(sidcnt,struct sidtable,0,"sids",sidcnt);
  bsids = basenet->sids;
  for (sid = 0; sid < bsidcnt; sid++) {
    bsp = bsids + sid;
    sp = sids + sid;
    sp->sid = bsp->sid;
    sp->t0 = bsp->t0;
    sp->t1 = bsp->t1;
    nlen = bsp->namelen;
    if (nlen) {
      memcpy(sp->name,bsp->name,nlen);
      sp->namelen = nlen;
    }
  }
  info(0,"%u sids",sidcnt);

  // routes
  ub4 cumrhops = 0,cumrhops2 = 0;

  ub4 ofs = 0;
  ub4 aid,hiaid = 0;
  ub4 nilridcnt = 0;

  enum carriers carrier,*carriercodes = glnet->carriercodes;
  ub4 carriercode;

  ridcnt = bridcnt + Croute_cnt;
  routes = alloc(ridcnt,struct route,0,"routes",ridcnt);
  broutes = basenet->routes;

  rp = routes + Croute_walk;
  rp->kind = Walk;

  rp = routes + Croute_taxi;
  rp->kind = Taxi;

  for (brid = 0; brid < bridcnt; brid++) {
    brp = broutes + brid;
    rid = brid + Croute_cnt;
    rp = routes + rid;
    rrid = brp->rrid;
    error_gt(rrid,hirrid,rid);
    rp->rrid = rrid;
    rp->rid = rid;
    if (rrid2rid[rrid]) return error(0,"duplicate rrid %u for %u",rrid,brid);
    rrid2rid[rrid] = rid;
    bkind = brp->kind;
    // if (bkind == Unknownb) bkind = Ferryb;
    error_eq_cc(bkind,Unknownb,"r.rid %u.%u %s",rp->rrid,rid,brp->name);
    error_ge(bkind,Kindcntb);
    rp->kind = bkind2kind(bkind,&rp->ckind);
    aid = brp->aid;
    rp->aid = aid;
    hiaid = max(hiaid,aid);

    rp->reserve = brp->reserve;
    rp->fare = brp->fare;
    rp->chainofs = brp->chainofs;
    rp->chaincnt = brp->chaincnt;
    cnt = rp->hopcnt = brp->hopcnt;
    if (cnt == 0) nilridcnt++;
    rp->hichainlen = brp->hichainlen;
    rp->lohop = hi32;
    rp->lochain = brp->lochain;

    nlen = brp->namelen;
    if (nlen) {
      memcpy(rp->name,brp->name,nlen);
      rp->namelen = nlen;
    }
    rp->hop2pos = ofs;
    ofs += cnt * cnt;
  }
  info(0,"%u routes in %u agencies",ridcnt,hiaid+1);
  warn(CC0,"%u route\as empty",nilridcnt);

  cumrhops = ofs;
  glnet->agencycnt = hiaid + 1;

  block *ridhopmem = &glnet->ridhopmem;
  glnet->ridhopbase = mkblock(ridhopmem,cumrhops + cumrhops2,ub4,Init1,"net");

  ub4 *gportsbyhop = alloc(bhopcnt * 2, ub4,0xff,"net portsbyhop",bhopcnt);
  ub4 dist,*hopdist = alloc(bhopcnt,ub4,0,"net hopdist",bhopcnt);
  ub4 midur;

  ub4 *drids,*arids,*deps,*arrs;
  ub4 t0,t1,tdep,prvtdep,evcnt;
  ub4 rsvhops = 0;
  const char *dname;

  ub4 hindep = 0,hinarr = 0,hidep = 0,hiarr = 0;
  ub4 prvrid;

  // transfers
  if (bxfercnt) {
    bxfers = bxp = basenet->xfers;
    xfers = xp = alloc(bxfercnt,struct xfer,0,"xfers",bxfercnt);
    memcpy(xfers,bxfers,bxfercnt * sizeof(struct xfer));
  }

  // hops
  hops = talloc(bhopcnt,struct hop,0,"hops",bhopcnt);
  hopcnt = 0;
  prvrid = 0;
  bhops = basenet->hops;
  for (hop = 0; hop < bhopcnt; hop++) {
    msgprefix(0,"hop %u",hop);
    bhp = bhops + hop;
    dep = bhp->dep;
    arr = bhp->arr;
    error_ge(dep,portcnt);
    error_ge(arr,portcnt);

    gportsbyhop[hop * 2] = dep;
    gportsbyhop[hop * 2 + 1] = arr;

    bpdep = bports + dep;
    bparr = bports + arr;
    dname = bpdep->iname;

    if (dep == arr) {
      return error(0,"nil hop %u %s at %u",dep,dname,bhp->id);
    } else if (bhp->evcnt == 0) {
      return error(0,"no evs for hop %u %s %s at %u",dep,dname,bparr->name,bhp->id);
    } else if (bhp->evcnt == 1) {
      warning(Iter,"1 ev for hop %u %s %s at %u",dep,dname,bparr->name,bhp->id);
    }

    pdep = ports + dep;
    parr = ports + arr;
    error_z(pdep->valid,hop); // todo
    error_z(parr->valid,hop);

    hp = hops + hop;
    hp->id = hop;
    nlen = bhp->namelen;
    if (nlen) {
      error_z(bhp->name[0],nlen);
      memcpy(hp->name,bhp->name,nlen);
      hp->namelen = nlen;
    } else info(0,"no name for dep %u arr %u",dep,arr);
    rrid = bhp->rrid;
    error_gt(rrid,hirrid,hop);
    hp->rrid = rrid;
    rid = rrid2rid[rrid];
    error_eq(rid,hi32);
    error_ge(rid,ridcnt);
    error_lt(rid,prvrid);
    prvrid = rid;
    hp->rid = rid;
    rp = routes + rid;

    rp->lohop = min(rp->lohop,hop);
    rp->hihop = max(rp->hihop,hop);

    hp->reserve = rp->reserve;
    if (rp->reserve) rsvhops++;
    hp->rhop = bhp->rhop;

    carriercode = bhp->carrier;
    if (carriercode == hi32) carrier = XX;
    else if (carriercode < hi16) carrier = carriercodes[bhp->carrier];
    else { warn(0,"hop %u unrecognised carrier code %c%c (%x)",hop,carriercode >> 8,carriercode & 0xff,carriercode); carrier = XX; }
    hp->carrier = carrier;

    tp = &hp->tp;
    btp = &bhp->tp;
    t0 = btp->t0;
    t1 = btp->t1;
    evcnt = bhp->evcnt;
    hp->evcnt = evcnt;

    tp->utcofs = btp->utcofs;
    tp->gt0 = btp->gt0;
    error_ne(tp->gt0,basenet->t0);
    tp->t0 = t0;
    tp->t1 = t1;

    tp->evofs = btp->evofs;
    infocc(hop == 0,0,"evofs %u",tp->evofs);
    tp->lodur = btp->lodur;
    tp->hidur = btp->hidur;
    midur = tp->midur = btp->midur;
    tp->avgdur = btp->avgdur;
    tp->duracc = btp->duracc;

    if (btp->overtake) hp->overtake = 1;

    // mark local links
    if ( ((hp->kind & Taxibit) && evcnt) || evcnt > 1) {
      pdep = ports + dep;
      parr = ports + arr;
      dcnt = pdep->ndep;
      deps = pdep->deps;
      drids = pdep->drids;
      if (dcnt == 0) {
        deps[0] = hop;
        drids[0] = rid;
        pdep->ndep = 1;
      } else if (dcnt == 1) {
        if (deps[0] != hop || drids[0] != rid) {
          deps[1] = hop;
          drids[1] = rid;
          pdep->ndep = 2;
        }
      } else if ( (deps[0] == hop && drids[0] == rid) || (deps[1] == hop && drids[1] == rid) ) ;
      else {
        pdep->ndep = ++dcnt;
        if (dcnt > hindep) { hindep = dcnt; hidep = dep; }
      }

      acnt = parr->narr;
      arrs = parr->arrs;
      arids = parr->arids;
      if (acnt == 0) {
        arrs[0] = hop;
        arids[0] = rid;
        parr->narr = 1;
      } else if (acnt == 1) {
        if (arrs[0] != hop || arids[0] != rid) {
          arrs[1] = hop;
          arids[1] = rid;
          parr->narr = 2;
        }
      } else if ( (arrs[0] == hop && arids[0] == rid) || (arrs[1] == hop && arids[1] == rid) ) ;
      else {
        parr->narr = ++acnt;
        if (acnt > hinarr) { hinarr = acnt; hiarr = dep; }
      }
    }

    hp->kind = rp->kind;

    hp->fare = bhp->fare;

    hp->varsda = bhp->varsda;
    hp->srdep = bhp->srdep;
    hp->srarr = bhp->srarr;

    dist = hp->dist = bhp->dist;
    hopdist[hop] = dist;
    error_z(dist,hop);

    hp->dep = dep;
    hp->arr = arr;
    hopcnt++;
    nomsgpfx();
  }
  if (hopcnt == 0) return error(0,"nil hops out of %u",bhopcnt);
  error_ne(hopcnt,bhopcnt);
  info(0,"\ah%u hops",hopcnt);
  info(CC0,"\ah%u of \ah%u hops reserved",rsvhops,hopcnt);
  // hopcnt = bhopcnt;

  pdep = ports + hidep;
  info(0,"highest ndep %u for port %u %s",hindep,hidep,pdep->name);
  for (hop = 0; hop < hopcnt; hop++) {
    hp = hops + hop;
    if (hp->dep != hidep) continue;
    arr = hp->arr;
    parr = ports + arr;
    info(V0," rid %u port %u %s",hp->rid,arr,parr->name);
  }
  parr = ports + hiarr;
  info(0,"highest narr %u for port %u %s",hinarr,hiarr,parr->name);
  for (hop = 0; hop < hopcnt; hop++) {
    hp = hops + hop;
    if (hp->arr != hiarr) continue;
    dep = hp->dep;
    pdep = ports + dep;
    info(V0," rid %u port %u %s",hp->rid,dep,pdep->name);
  }

  // free base hops
  afree(basenet->hops,"base hops");

  // prepare <rid,dep,arr> to hop lookup
  ub4 rhop,rhopovf = 0;

  for (hop = 0; hop < hopcnt; hop++) {
    hp = hops + hop;
    rid = hp->rid;
    if (rid == hi32) continue;
    error_ge(rid,ridcnt);
    rp = routes + rid;
    rhop = hp->rhop;
    if (rhop < Chainlen) rp->hops[rhop] = hop;
    else rhopovf++;
  }
  warncc(rhopovf,0,"%u of %u hops exceeding %u chain limit",rhopovf,hopcnt,Chainlen);

  ub4 *bbox = glnet->bbox;

  // bbox of connected ports
  for (port = 0; port < portcnt; port++) {
    pp = ports + port;
    if (pp->ndep == 0 && pp->narr == 0) continue;
    updbbox(pp->lat,pp->lon,bbox,Elemcnt(glnet->bbox));
  }
  info(0,"bbox lat %u - %u = %u",bbox[Minlat],bbox[Maxlat],bbox[Latrng]);
  info(0,"bbox lon %u - %u = %u",bbox[Minlon],bbox[Maxlon],bbox[Lonrng]);

  ub4 i,idx,bofs,seq,prvseq,rtid;

  // chains
  chains = alloc(bchaincnt,struct chain,0,"chains",bchaincnt);
  bchains = basenet->chains;
  bchainhops = basenet->chainhops;
  bchainidxs = basenet->chainidxs;
  chaincnt = chainhopcnt = ofs = 0;
  ub4 rcnt,rofs = 0;
  prvrid = 0;
  for (chain = 0; chain < bchaincnt; chain++) {
    bcp = bchains + chain;
    cp = chains + chain;
    brid = bcp->rid;
    rrid = bcp->rrid;
    error_lt(brid,prvrid);
    prvrid = brid;
    error_gt(rrid,hirrid,chain);
    rid = rrid2rid[rrid];
    cp->rid = rid;
    cp->tripno = bcp->tripno;
    cnt = bcp->hopcnt;
    rp = routes + rid;
    if (cnt == 0) info(Iter,"route %u %s: dummy chain %u with %u hop\as",rp->rrid,rp->name,chain,cnt);
    if (chain < rp->lochain) return error(0,"route %u %s: unsorted chain %u after %u",rp->rrid,rp->name,chain,rp->lochain);
    rp->hichain = max(rp->hichain,chain);

    rcnt = rp->hopcnt;
    cp->hopcnt = cnt;
    cp->rhopcnt = rcnt;
    cp->rrid = bcp->rrid;
    cp->rtid = bcp->rtid;
    cp->dtid = bcp->dtid;
    cp->hopofs = ofs;
    cp->rhopofs = rofs;
    ofs += cnt;
    rofs += rcnt;
    chaincnt++;
  }
  chainhopcnt = ofs;
  error_ne(chaincnt,bchaincnt);
  info(0,"\ah%u chains with \ah%u hops",chaincnt,chainhopcnt);

  ub4 *tid2rtid = alloc(chaincnt,ub4,0,"chain tid2rtid",chaincnt);
  struct chainhop *chp,*chainhops = alloc(chainhopcnt,struct chainhop,0,"chain hops",chainhopcnt);

  ub2 *chrp,*chainrhops = alloc(rofs,ub2,0xff,"chain rhops",cumrhops);

  ub4 loopcnt = 0;
  ub4 starthop,endhop;

  // write in sorted order
  for (chain = 0; chain < chaincnt; chain++) {
    cp = chains + chain;
    bcp = bchains + chain;
    cnt = cp->hopcnt;
    rtid = cp->rtid;
    tid2rtid[chain] = rtid;
    if (cnt == 0) continue;
    rid = cp->rid;
    rp = routes + rid;

    ofs = cp->hopofs;
    bofs = bcp->hopofs;
    bchip = bchainidxs + bofs;
    seq = prvtdep = 0;
    chrp = chainrhops + cp->rhopofs;
    for (i = 0; i < cnt; i++) {
      chp = chainhops + ofs + i;
      idx = bchip[i] & hi32;
      error_ge(idx,cnt);
      bchp = bchainhops + bofs + idx;
      error_ne(chain,bchp->chain);
      prvseq = seq;
      seq = (ub4)(bchip[i] >> 32);
      hop = bchp->hop;
      tdep = bchp->tdep;
      error_le(seq,prvseq);
      chp->hop = hop;
      chp->chain = chain;
      chp->tdep = tdep;
      hp = hops + hop;
      rhop = hop - rp->lohop;
      error_ge(rhop,rp->hopcnt);
//      rhop = hp->rhop;
//      error_ge(rhop,cp->rhopcnt);
      if (cnt > 1) chrp[rhop] = (ub2)i;
      if (tdep < prvtdep) {  // todo day wrap ?
        warn(0,"rid %u rtid %u tdep %u before prvtdep %u %s",rid,rtid,tdep,prvtdep,rp->name);
        cp->hopcnt = i;
        break;
      }
      prvtdep = tdep;
      chp->tarr = bchp->tarr;
      error_lt(chp->tarr,chp->tdep);
      chp->midur = bchp->midur;
      chp->seq = bchp->seq;
      chp->srda = bchp->srda;
    }

    if (cnt > 2) {
      starthop = chainhops[ofs].hop;
      hp = hops + starthop;
      endhop = chainhops[ofs+cnt-1].hop;
      hp2 = hops + endhop;
      pdep = ports + hp->dep;
      if (hp->dep == hp2->arr && hp->arr != hp2->dep && rp->loop == 0) {
        pdep = ports + hp->dep;
        pdep->loop = 1;
        info(Notty|Iter,"rid %u len %u loop at port %u %s %s",rid,cnt,hp->dep,rp->name,pdep->iname);
        rp->loop = 1;
        loopcnt++;
        rp->startport = hp->dep;
      }
    }
  }
  info(CC0,"%u of %u routes are loops",loopcnt,ridcnt);
  afree0(bchains);
  afree0(bchainhops);
  afree0(bchainidxs);

  ub4 oneridcnt = 0;
  ub4 onerid;
  bool oneroute;
  ub4 ndep,narr;

  // mark single-route only ports
  for (port = 0; port < portcnt; port++) {
    pp = ports + port;
    if (pp->loop) continue;
    ndep = pp->ndep;
    narr = pp->narr;
    drids = pp->drids;
    arids = pp->arids;
    arrs = pp->arrs;
    deps = pp->deps;

    pp->nda = ndep + narr;

    oneroute = 0; onerid = 0;
    if (pp->geo == 0 && ndep == 0 && narr == 0) {
      pp->valid = 0;
      continue;
    }
    else if (ndep > 2 || narr > 2) continue;
    else if (ndep == 0 && narr == 1 && arids[0] != hi32) {
      oneroute = 1;
      onerid = arids[0];
    } else if (ndep == 1 && narr == 0 && drids[0] != hi32) {
      oneroute = 1;
      onerid = drids[0];
    } else if (ndep == 1 && narr == 1 && drids[0] == arids[0] && drids[0] != hi32) {
      oneroute = 1;
      onerid = arids[0];
    } else if (ndep == 2 && narr == 2 && drids[0] != hi32 && drids[1] != hi32) {
      if (drids[0] == drids[1] && arids[0] == arids[1] && drids[0] == arids[0]) {
        oneroute = 1;
        onerid = arids[0];
#if 0
      } else if (drids[0] == arids[0] && drids[1] == arids[1]) {
        if (sameroute2a(hops,port,drids,deps,arrs)) {
          oneroute = 1;
          onerid = arids[0];
        }
      } else if (drids[0] == arids[1] && drids[1] == arids[0]) {
        if (sameroute2b(hops,port,drids,deps,arrs)) {
          oneroute = 1;
          onerid = arids[0];
        }
#endif
      }
    }
    if (oneroute) {
      pp->oneroute = 1;
      pp->onerid = onerid;
      oneridcnt++;
    }
  }
  info(CC0,"\ah%u of \ah%u ports on one route",oneridcnt,portcnt);

  glnet->portcnt = portcnt;
  glnet->sportcnt = sportcnt;
  glnet->hopcnt = hopcnt;
  glnet->sidcnt = sidcnt;
  glnet->chaincnt = chaincnt;
  glnet->ridcnt = ridcnt;
  glnet->xfercnt = xfercnt;
  glnet->xfers = xfers;

  glnet->ports = ports;
  glnet->sports = sports;
  glnet->hops = hops;
  glnet->sids = sids;
  glnet->chains = chains;
  glnet->routes = routes;

  glnet->portsbyhop = gportsbyhop;
  glnet->hopdist = hopdist;

  glnet->chainhops = chainhops;
  glnet->chainrhops = chainrhops;
  glnet->chainhopcnt = chainhopcnt;
  glnet->routechains = basenet->routechains;

  glnet->latscale = basenet->latscale;
  glnet->lonscale = basenet->lonscale;

  glnet->hirrid = hirrid;
  glnet->rrid2rid = rrid2rid;

  glnet->tid2rtid = tid2rtid;
  glnet->hichainlen = basenet->hichainlen;

  glnet->eventmem = &basenet->eventmem;
  glnet->events = basenet->events;
  glnet->t0 = basenet->t0;
  glnet->t1 = basenet->t1;
  glnet->tt0 = basenet->tt0;
  glnet->tt1 = basenet->tt1;

  glnet->feedstamp = basenet->feedstamp;
  glnet->feedlostamp = basenet->feedlostamp;

  glnet->walklimit = m2geo(globs.walklimit);
  glnet->sumwalklimit = m2geo(globs.sumwalklimit);

  glnet->net1walklimit = m2geo(globs.net1walklimit);
  glnet->net2walklimit = m2geo(globs.net2walklimit);

  info(0,"precomputed walk limit set to %u m, summed %u",globs.walklimit,globs.sumwalklimit);

  prepgeo(glnet);

  // write reference for name lookup
  if (dorun(FLN,Runserver,1) && wrportrefs(basenet,bbox)) return 1;

  return 0;
}
