// compound.c - create compound hops from routes

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2017 Joris van der Geer.
 */

/*
  Add virtual non-stop hops between any two ports on the same route.
  A route is defined here as in public transport : ports are visited in succession
  without actual tranfers.

  Such compound hop points to its first and last actual hop.
  These in turn contain the depart and arrive times.

  Create events for both original and compound hops. Compress these by finding repetition on 24-hour periods
 */

#include <string.h>
#include <stdarg.h>

#include "base.h"
#include "cfg.h"
#include "mem.h"
#include "math.h"

static ub4 msgfile;
#include "msg.h"

#include "iadr.h"
#include "util.h"
#include "net.h"
#include "compound.h"

#undef hdrstop

/* count base evs
   estimate cmp hopcount
   allocate cmp hops
   estimate cmp events
   estimate eqsda
   allocate events and sda, to be trimmed after compress
   per rid {
     create base events
     create cmp hops
     create cmp events
   }
 */

static const ub4 cmp_maxperm = 150;	       // permutations per compound route
static const ub4 cmp_maxperm2 = 120 * 120;

static const ub4 cmp_maxev = 1440 * 90 / 3;    // events per hop

static const ub4 daymin = 1440;

static const int do_rndfares = 0;

static int docombine = 0; // create combined aka connected hops: wip

// range of unencoded accels
#define Iacclen 65536
#define Iacclim (Iacclen-1)

sassert(Iacclen <= (1U << 16),"accel <= 16 bits") sassert_end

// revents: dtid | dur | rt

void inicompound(void)
{
  msgfile = setmsgfile(__FILE__);
  iniassert();
}

struct refev {
  ub4 hop;
  ub4 pos,len,dt,tday0;
  ub4 rday;
  ub8 timchk;
};

struct thop {  // aux data
  ub4 hop;
  ub4 tidpos,tidofs;
  ub4 acc1ei,acc2ei,acc3ei; // ev pos of first interval

  ub1 init1; // base evs
  ub1 init2; // events
};

static ub8 acchist8[Iacclen];

static ub4 mkacc(ub4 *hist,ub2 *tab,ub2 *itab,ub4 len,ub4 *plimcnt,const char *desc)
{
  nsethi(itab,Iacclen);

  ub4 iaclen,iacndx = 0;
  ub4 cnt,acc,lastacc,i;

  // create accel lookup tables
  for (acc = 0; acc < Iacclen; acc++) {
    cnt = hist[acc];
    if (cnt) iacndx++;
    acchist8[acc] = ((ub8)cnt << 32) | acc;
  }
  iaclen = iacndx;
  infocc(iaclen > len,0,"%u %s acc entries, max %u",iaclen,desc,len);
  sort8(acchist8,Iacclen,FLN,"acc" );

  nsethi(tab,len);

  i = Iacclen - 1;
  iacndx = 0;
  cnt = 0;
  while (iacndx < len && i) {
    cnt = acchist8[i] >> 32;
    if (cnt == 0) break;
    acc = acchist8[i] & Iacclim;
    tab[iacndx] = (ub2)max(acc,1);
    itab[acc] = (ub2)iacndx;
    iacndx++;
    i--;
  }
  error_gt(iacndx,iaclen,0);
  if (iacndx == len) {
    warn(0,"%s acc hr1 hi index %u at cnt %u",desc,iacndx,cnt);
    (*plimcnt)++;
  } else if (iacndx == 0) {
    warn(0,"%s acc hr1 hi index 0 at cnt %u",desc,cnt);
  } else {
    info(0,"%s acc hr1 len %u at cnt %u",desc,iacndx,cnt);
  }
  iaclen = iacndx;

  // refer missing entries to nearest lower
  lastacc = iacndx;
  if (lastacc) lastacc--;
  for (acc = 0; acc < Iacclen; acc++) {
    iacndx = itab[acc];
    if (iacndx == hi16) itab[acc] = (ub2)lastacc;
    else lastacc = iacndx;
  }
  for (acc = 0; acc < Iacclen; acc++) {
    iacndx = itab[acc];
    error_ge(iacndx,iaclen);
  }
  return iaclen;
}

// add compound hops
static int do_compound(gnet *net,int docompound,int do_compress)
{
  ub4 rportcnt,rport2,portcnt = net->portcnt;
  ub4 hopcnt = net->hopcnt;
  ub4 hop,chop,zchop,chopcnt,newhopcnt = 0,newcnt;
  ub4 rid,rrid,ridcnt = net->ridcnt;
  ub4 chain,rchaincnt,chaincnt = net->chaincnt;

  ub4 hichainlen = net->hichainlen;

  struct hop *hp,*hp1,*hp2,*hops = net->hops;
  struct port *pdep,*parr,*ports = net->ports;
  struct route *rp,*routes = net->routes;
  struct chain *cp,*chains = net->chains;
  struct chainhop *cnhp,*chainhops = net->chainhops;
  ub2 *crp,*chainrhops = net->chainrhops;

  ub4 maxperm = min(cmp_maxperm,Chainlen);

  ub4 dep,arr,deparr,rdep,rarr;

  net->chopcnt = hopcnt;

  ub4 *orgportsbyhop = net->portsbyhop;
  ub4 *orghopdist = net->hopdist;

  ub4 midur,dur,dur1;

  ub4 hop1,hop2,rhop1,rhop2,rhop12,dep1,arr2;
  ub4 dist1,dist2,dist = 0,dirdist;
  ub4 tdep,tarr,tdep1,tarr2;
  ub4 ci,ci1,ci2,ci3,cimid,cilast,pchlen,pchlen2,cmpcnt;

  ub4 pchain[Chainlen];
  ub4 pdeps[Chainlen];
  ub4 parrs[Chainlen];
  ub4 ptdep[Chainlen];
  ub4 ptarr[Chainlen];
  ub4 ptarrseq[Chainlen];
  ub4 pdist[Chainlen];
  ub4 psrda[Chainlen];

  error_zp(orghopdist,hopcnt);

  ub4 cnt,cmphopcnt = 0;

  error_z(chaincnt,ridcnt);

  error_zp(routes,0);
  error_zp(chains,0);

  struct eta eta;
  int warnlim;

  ub8 cumbevcnt = 0,cumcevcnt = 0,cumevcnt,p1cevcnt = 0,cumfevcnt = 0,cumcfevcnt = 0,cofs = 0;
  ub4 sumnocevcnt = 0;
  ub8 p1evcnt = 0,p2evcnt = 0;
  ub4 evcnt,evcnt1,evcnt2,cevcnt,hirevcnt = 0,ridevcnt = 0;
  ub4 cumfhops = 0;
  ub4 varbsda = 0,varcsda = 0;
  ub4 hicnt = 0,hirid = 0,hievrid = 0,hiridhopcnt = 0,hihoprid = 0;

  for (rid = 0; rid < ridcnt; rid++) {
    rp = routes + rid;
    // error_z(rp->chaincnt,rid);
    if (rp->hopcnt > hicnt) { hicnt = rp->hopcnt; hirid = rid; }
  }
  rp = routes + hirid;
  info(0,"r.rid %u.%u has %u hops for len %u",rp->rrid,hirid,hicnt,rp->hichainlen);
  warncc(hicnt > cmp_maxperm,0,"r.rid %u.%u len %u above limit %u",rp->rrid,hirid,hicnt,cmp_maxperm);

  ub4 hirhopcnt = hicnt;
  error_lt(hirhopcnt,hichainlen);
  ub4 hirhopcnt2 = hicnt * hicnt;

  error_zz(hichainlen,hicnt);
  ub4 hiportlen = max(hichainlen,hicnt) + 10;
  ub4 hiport2 = hiportlen * hiportlen;

  ub4 *port2rport = talloc(portcnt,ub4,0,"cmp rportmap",portcnt);
  ub4 *rport2port = talloc(hiportlen,ub4,0,"cmp rportmap",hiportlen);

  ub4 *duphops = talloc(hirhopcnt2,ub4,0xff,"cmp duphops",hirhopcnt); // stores chop

  ub4 dupda,*dupdas = talloc(hiport2,ub4,0,"cmp dupdas",hiportlen); // stores ci1 | ci2

  ub1 *bidirhops = talloc(hirhopcnt2,ub1,0,"cmp bidir",hirhopcnt);
  ub4 *depcnts = talloc(hirhopcnt,ub4,0,"cmp bidir",0);
  ub4 *arrcnts = talloc(hirhopcnt,ub4,0,"cmp bidir",0);

  ub4 *grpndxs = talloc(hirhopcnt,ub4,0,"cmp grpndx",0);

  ub4 gt0 = net->t0;

  ub4 grpndx,gndx1,gndx2,gndxl,gndxh,rhop,rhopcnt,rhopcnt2;
  ub4 lohop,dtid;

  ub4 n2,cbidircnt,bidircnt = 0,ridlimcnt = 0,splitcnt = 0;
  ub4 varcsdacnt = 0,varbsdacnt = 0;
  ub8 varbsdalen = 0,varcsdalen = 0;
  bool isround;
  bool dbg = 0;

  error_ge(hopcnt,hi32 - 1);

  ub4 cmpcntlim = hi32 - hopcnt;

  ub4 hoptidlen = 0;

  ub4 hievcnt = 0,hievhop = 0,hihopcnt = 0;

  for (hop = 0; hop < hopcnt; hop++) {
    hp = hops + hop;
    error_eq(hp->rid,hi32);
    hp->tripstart = hp->tripend = 1;
    dep = orgportsbyhop[hop * 2];
    arr = orgportsbyhop[hop * 2 + 1];
    error_ge(dep,portcnt);
    error_ge(arr,portcnt);
    evcnt = hp->evcnt;
    if (evcnt > cmp_maxev) {
      warn(0,"hop %u evs %u above max %u",hop,evcnt,cmp_maxev);
      evcnt = hp->evcnt = cmp_maxev;
    }
    if (evcnt > hievcnt) { hievcnt = evcnt; hievhop = hop; }
    cumbevcnt += evcnt;
    if (hp->varsda) {
      varbsda++;
      varbsdalen += evcnt;
    }
    if (hp->reserve) {
      cumfevcnt += evcnt;
      cumfhops++;
    }
  }
  info(0,"\ah%lu base events \ah%lu varsda",cumbevcnt,varbsdalen);
  info(CC0,"\ah%lu fare events in \ah%u hops",cumfevcnt,cumfhops);
  info(CC0,"\ah%u of \ah%u hops with variable sub deparr",varbsda,hopcnt);
  info(0,"hi hop %u hi evs %u",hihopcnt,hievcnt);

  // pass 1: count
  for (rid = 0; rid < ridcnt; rid++) {

    evcnt = cevcnt = 0;

    if (progress(&eta,"pass 1  rid %u of %u hops \ah%u evs \ah%lu",rid,ridcnt,cmphopcnt,p1cevcnt)) return 1;
    rp = routes + rid;
    if (rp->kind == Airint || rp->kind == Airdom) continue;
    rhopcnt = rp->hopcnt;
    if (rhopcnt < 2) { info(V0,"p1 rid %02u skip on %u hop\as",rid,rhopcnt); continue; }
    rhopcnt2 = rhopcnt * rhopcnt;

    lohop = rp->lohop;

    msgprefix(0,"p1 rid %02u",rid);

    error_ne(rhopcnt,rp->hihop - lohop + 1);
    rrid = rp->rrid;

    hihopcnt = max(hihopcnt,rhopcnt);

    nsethi(port2rport,portcnt);
    nsethi(grpndxs,rhopcnt);

    rportcnt = 0;
    rchaincnt = 0;
    cbidircnt = 0;
    grpndx = 0;

    for (hop = lohop; hop <= rp->hihop; hop++) {
      error_ge(hop,hopcnt);
      rhop = hop - lohop;
      hp = hops + hop;
      error_ne(hp->rid,rid);

      error_le(hi32 - hp->evcnt,evcnt);
      evcnt += hp->evcnt;

      error_ge(hoptidlen,hi32 - rp->chaincnt);

      dep = hp->dep;
      arr = hp->arr;
      error_eq(dep,arr);

      if (dbg) {
        pdep = ports + dep;
        parr = ports + arr;
        info(0,"hop %u %s %s %s",hop,hp->name,pdep->name,parr->name);
      }

      if (port2rport[dep] == hi32) {
        error_ge(rportcnt,hiportlen);
        port2rport[dep] = rportcnt;
        rport2port[rportcnt++] = dep;
      }
      if (port2rport[arr] == hi32) {
        error_ge_cc(rportcnt,hiportlen,"rrid %u len %u cnt %u",rrid,rp->hichainlen,rp->hopcnt);
        port2rport[arr] = rportcnt;
        rport2port[rportcnt++] = arr;
      }
    }
    error_z(rportcnt,rp->hihop);

    warncc(rportcnt >= hiportlen,0,"r.rid %u.%u len %u above %u",rrid,rid,rportcnt,hiportlen);
    rportcnt = min(rportcnt,hiportlen);
    error_ovf(rportcnt,ub2);
    rport2 = rportcnt * rportcnt;
    nsethi(duphops,rhopcnt2);
    newcnt = 0;

    infocc(dbg,Iter,"chains %u..%u",rp->lochain,rp->lochain + rp->chaincnt);

    warnlim = 1;
    for (chain = rp->lochain; docompound && chain < rp->lochain + rp->chaincnt; chain++) {
      dtid = chain - rp->lochain;
      cp = chains + chain;
      cnt = cp->hopcnt;
      error_ne(cp->rid,rid);

      if (cnt < 2) continue;

      pchlen = 0;
      for (ci = 0; ci < cnt; ci++) {
        cnhp = chainhops + cp->hopofs + ci;
        hop = cnhp->hop;
        error_ge(hop,hopcnt);
        hp = hops + hop;
        error_ne(hp->rid,rid);

        if (pchlen == maxperm) {
          if (warnlim) {
            ridlimcnt++;
            warn(Iter,"limiting rid %u chain to %u %s",rid,maxperm,rp->name);
            warnlim = 0;
          }
          break;
        }

        dep = hp->dep;
        arr = hp->arr;
        if (dep == arr) continue;

        rdep = port2rport[dep];
        rarr = port2rport[arr];
        error_ge_cc(rdep,rportcnt,"hop %u %u-%u",hop,dep,arr);
        error_ge(rarr,rportcnt);

        pchain[pchlen] = hop;
        pdeps[pchlen] = rdep;
        parrs[pchlen] = rarr;
        depcnts[rdep]++;
        arrcnts[rarr]++;

        tdep = cnhp->tdep;
        tarr = cnhp->tarr;
        error_lt(tarr,tdep);
        pchlen++;
      }
      if (pchlen < 2) continue;
      error_gt(pchlen,rhopcnt,chain);
      pchlen2 = pchlen * pchlen;
      rchaincnt++;

      // check if roundtrip: a-b-c-b-a  versus a-b-c-d-e
      cilast = pchlen - 1; cimid = 0;
      isround = (arrcnts[0] == 1 && depcnts[0] == 1 && depcnts[cilast] == 1 && arrcnts[cilast] == 1);

      n2 = 0;
      if (isround) {
        for (ci1 = 1; ci1 < cilast; ci1++) {
          if (arrcnts[ci1] == 2 && depcnts[ci1] == 2) n2++;
          else if (arrcnts[ci1] == 1 && depcnts[ci1] == 1) { cimid = ci1; break; }
          else break;
        }
        isround = (ci1 == pchlen && cimid);
      }

      // todo: not used mark only 2 single chains for compound
      if (isround) {
        info(0,"rid %u roundtrip %s",rid,rp->name);
        cbidircnt++;
//        if (n2 == 0) break; // a-c-a
        nclear(bidirhops,pchlen2);
        for (ci1 = 0; ci1 < cimid; ci1++) {
          error_ge(cimid,hi32 - 16);
          error_ge(ci1,hi32 - 16);
          error_ge(ci1,(hi32 - cimid) / rhopcnt);
          error_ge(cimid,(hi32 - cimid) / rhopcnt);
          error_z(cimid,0);
          ci2 = ci1 + 1;
          error_ge(ci2,hi32 - 16);
          error_ge(ci1,cimid);
          Diagoff
          while (ci2 <= cimid) {
            bidirhops[ci1 * rhopcnt + ci2] = 1;
            ci2++;
          }
          Diagon
        }
        for (ci1 = cimid; ci1 < cilast; ci1++) {
          for (ci2 = ci1 + 1; ci2 < pchlen; ci2++) bidirhops[ci1 * rhopcnt + ci2] = 1;
        }
      }

      // generate all not yet existing compounds
      cmpcnt = 0;
      for (ci1 = 0; ci1 < pchlen - 1; ci1++) {
        dep1 = pdeps[ci1];
        hop1 = pchain[ci1];
        rhop1 = hop1 - lohop;
        for (ci2 = ci1 + 1; ci2 < pchlen; ci2++) {
          arr2 = parrs[ci2];
          if (dep1 == arr2) continue;

          hop2 = pchain[ci2];
          rhop2 = hop2 - lohop;
          rhop12 = rhop1 * rhopcnt + rhop2;
          error_ge(rhop12,rhopcnt2);
          if (duphops[rhop12] != hi32) continue;

          deparr = dep1 * rportcnt + arr2;  // filter redundant options in looping trips
          error_ge(deparr,rport2);
          dupda = dupdas[deparr];
          if (dupda != hi32) {
            for (ci3 = 0; ci3 < ci2; ci3++) {
              if (parrs[ci3] == arr2) break;
            }
            if (ci3 < ci2) continue;
          } else dupdas[deparr] = ci1 << 16 | ci2;

          duphops[rhop12] = dtid;
          cmpcnt++;

          // estimate events, recognise split routes and mark trip ends
          hp1 = hops + hop1;
          hp2 = hops + hop2;
          error_ne(hp1->rid,rid);
          error_ne(hp2->rid,rid);

          hievcnt = max(hievcnt,hp1->evcnt);

          error_le(hi32 - hp1->evcnt,cevcnt);
          cevcnt += hp1->evcnt;  // tentative

          if (hp1->varsda || hp2->varsda) { // tentative
            varcsdacnt++;
            varcsdalen += hp1->evcnt;
          }

          if (ci1 != 0) hp1->tripstart = 0;
          hp1->tripend = 0;
          if (ci2 != pchlen - 1) hp2->tripend = 0;
          hp2->tripstart = 0;
          error_ge(rhop1,rhopcnt);
          error_ge(rhop2,rhopcnt);
          gndx1 = grpndxs[rhop1];
          gndx2 = grpndxs[rhop2];
          if (gndx1 == hi32 && gndx2 == hi32) {
            grpndxs[rhop1] = grpndxs[rhop2] = hp1->grp = hp2->grp = grpndx++;
          } else if (gndx1 == hi32 || gndx2 == hi32) {
            grpndxs[rhop1] = grpndxs[rhop2] = hp1->grp = hp2->grp = min(gndx1,gndx2);
          } else if (gndx1 != gndx2) {
            gndxl = min(gndx1,gndx2);
            gndxh = max(gndx1,gndx2);
            for (rhop = 0; rhop < rhopcnt; rhop++) {
              if (grpndxs[rhop] == gndxh) grpndxs[rhop] = hp1->grp = hp2->grp = gndxl;
            }
          }

          // if (cmpcnt + newcnt >= cmp_maxperm2) break;
        } // each c2
        if (cmpcnt + newcnt >= cmp_maxperm2) {
          if (warnlim) {
            ridlimcnt++;
            warn(Iter,"reaching %u combis for compound on rid %u",cmpcnt,rid);
            warnlim = 0;
          }
          // break;
        }
      } // each c1

      error_ge(newcnt,cmpcntlim - cmpcnt);

      newcnt += cmpcnt;
      if (newcnt >= cmp_maxperm2) {
        warn(Iter,"reaching %u combis for compound on rid %u",newcnt,rid);
        break;
      }
    } // each chain

    error_ge(cmphopcnt,cmpcntlim - newcnt);
    cmphopcnt += newcnt;
    info(0,"%u cmp hops",newcnt);

    cnt = newcnt + rhopcnt;
    if (cnt > hiridhopcnt) {
       hiridhopcnt = cnt;
       hihoprid = rid;
    }

    p1cevcnt += cevcnt;

    error_le(hi32 - cevcnt,evcnt);
    ridevcnt = evcnt + cevcnt;
    if (ridevcnt > hirevcnt) {
      hirevcnt = ridevcnt;
      hievrid = rid;
    }

    info(Iter|V0,"rid %u len %u cmp %u cevs %u bevs %u",rid,rportcnt,newcnt,cevcnt,evcnt);
    infocc(cbidircnt,Iter,"rid %u chains %u bidir %u",rid,rchaincnt,cbidircnt);
    bidircnt += cbidircnt;

    gndxl = hi32; gndxh = 0;
    for (rhop = 0; rhop < rhopcnt; rhop++) {
      gndx1 = grpndxs[rhop];
      if (gndx1 == hi32) continue;
      gndxh = max(gndxh,gndx1);
      gndxl = min(gndxl,gndx1);
    }

    grpndx = gndxh - gndxl;
    if (grpndx > 2) {
      splitcnt++;
      info(Iter,"rid %u split in %u groups %s",rid,grpndx,rp->name);
      warncc(grpndx > 4,0,"rid %u split in %u groups %s",rid,grpndx,rp->name);
      if (dbg) {
        for (hop = 0; hop < hopcnt; hop++) {
          hp = hops + hop;
          if (hp->rid != rid) continue;
          pdep = ports + hp->dep;
          parr = ports + hp->arr;
          info(0,"hop %u grp %u %s - %s",hop,hp->grp,pdep->iname,parr->name);
        }
      }
    }
    hoptidlen = max(hoptidlen,cevcnt);
  } // each rid
  nomsgpfx();

  if (docompound) {
    info(Emp,"\ah%u compound hops added to \ah%u, %u bidir %u total",cmphopcnt,hopcnt,bidircnt,cmphopcnt + hopcnt);
    info(Emp,"\ah%lu tentative cevents",p1cevcnt);
    info(CC0,"\ah%u of \ah%u cmp hops with variable sub deparr",varcsda,cmphopcnt);
    info(CC0,"\ah%u of \ah%u rids limited by %u,%u",ridlimcnt,ridcnt,maxperm,cmp_maxperm2);
    info(CC0,"%u of %u split routes",splitcnt,ridcnt);
    info(0,"rid %u has \ah%u tentative events",hievrid,hirevcnt);
    info(0,"rid %u has %u hops",hihoprid,hiridhopcnt);
    info(0,"max tid len \ah%u",hoptidlen);
  }

  cumcevcnt = p1cevcnt;
  p1evcnt = cumbevcnt + p1cevcnt;
  ridevcnt = hirevcnt;
  ub4 startcnt = 0,endcnt = 0,pstartcnt = 0,pendcnt = 0;
  for (hop = 0; hop < hopcnt; hop++) {
    hp = hops + hop;
    dep = hp->dep;
    arr = hp->arr;
    pdep = ports + dep;
    parr = ports + arr;
    if (hp->tripstart) { startcnt++; pdep->tripstart = parr->tripstart = 1; }
    if (hp->tripend) { endcnt++; pdep->tripend = parr->tripend = 1; }
  }
  for (dep = 0; dep < portcnt; dep++) {
    pdep = ports + dep;
    if (pdep->tripstart) pstartcnt++;
    if (pdep->tripend) pendcnt++;
  }

  info(CC0,"%u of %u = \ap%lu%lu hops at trip start",startcnt,hopcnt,(ub8)startcnt,(ub8)hopcnt);
  info(CC0,"%u of %u = \ap%lu%lu hops at trip end",endcnt,hopcnt,(ub8)endcnt,(ub8)hopcnt);
  info(CC0,"%u of %u = \ap%lu%lu ports at trip start",pstartcnt,portcnt,(ub8)pstartcnt,(ub8)portcnt);
  msgopt("pass1"); info(CC0,"%u of %u = \ap%lu%lu ports at trip end",pendcnt,portcnt,(ub8)pendcnt,(ub8)portcnt);

  info(0,"compound %u chains in %u rids pass 2",chaincnt,ridcnt);

  // tmp store for events per rid

  info(Emp,"max %u evs, %u hops, \ah%u max rid events",hievcnt,hihopcnt,ridevcnt);

  ub8 rx,*rev,*rev1,*revr,*ridevents = talloc(ridevcnt,ub8,0,"rid events dur,t",ridevcnt);  // dtid | dur | t

  newhopcnt = cmphopcnt + hopcnt;

  // create cmp hops here
  struct chop *chp,*chp1,*chops = net->chops = alloc(newhopcnt,struct chop,0,"chops",newhopcnt);
  struct thop *thp,*thp1,*thops = talloc(newhopcnt,struct thop,0,"thops",newhopcnt);
  chop = net->chopcnt = hopcnt;

  ub4 *portsbyhop = alloc(newhopcnt * 2,ub4,0,"cmp portsbyhop",newhopcnt);
  memcpy(portsbyhop,orgportsbyhop,hopcnt * 2 * sizeof(ub4));
  afree(orgportsbyhop,"net portsbyhop");
  net->portsbyhop = portsbyhop;

  ub4 *hopdist = alloc(newhopcnt,ub4,0,"cmp hopdist",newhopcnt);
  memcpy(hopdist,orghopdist,hopcnt * sizeof(ub4));
  afree(orghopdist,"net hopdist");
  net->hopdist = hopdist;

  ub4 *hdp1,*hopdtidlst = NULL;

  ub8 rsx,*hsp1,*hopstlst = NULL;

  ub8 *h12p,*hop12lst = NULL;
  ub4 xhop1,xhop2;
  ub4 *hhp,*hophlst = NULL;

  if (docompound) {
    hopdtidlst = talloc(hoptidlen,ub4,0,"dtid list",0);
    hopstlst = talloc(hoptidlen,ub8,0,"srda,dur lst",0);   // srda | dur
    hop12lst = talloc(hoptidlen,ub8,0,"hop12 lst",0);   // hop1 | hop2
    hophlst = talloc(hoptidlen,ub4,0,"chk lst",0);
  }

  ub8 bx,bx1,*bev,*bevents = net->events;
  ub4 bevcnt;
  ub4 bei,rei,acc1ei,acc2ei,acc3ei;
  ub4 rt,prvt,acc1rt,acc2rt,acc3rt;
  ub4 tid,tidlen1;

  ub8 cumchainlen = 0,pchaincnt = 0;
  ub4 revofs,revofsr;
  ub8 cevofs = 0;
  ub4 eqdurs = 0,aeqdurs = 0;
  ub4 cdist;
  ub4 idx1,idx2,ndx1;
  ub4 srda,srda1,srdep1,srarr1,srdep2,srarr2,prvsrdep1 = hi32,prvsrarr2 = hi16;
  ub4 lochop,prvchop,curchop,tidofs,tidofs1,curtidofs,tidpos,pos;
  ub4 c1;

  // count and copy basics
  ub4 nocmpev,nocmpev1,nocmpev2,acclimcnt;

  ub4 overtakecnt = 0;

  for (hop = 0; hop < hopcnt; hop++) {
    hp = hops + hop;
    chp = chops + hop;
    rid = hp->rid;
    rp = routes + rid;

    if (hp->overtake) { chp->overtake = 1; overtakecnt++; }
    evcnt = hp->evcnt;
    dep = hp->dep;
    arr = hp->arr;
    error_ne(dep,portsbyhop[hop * 2]);
    error_ne(arr,portsbyhop[hop * 2 + 1]);
    chp->dep = dep;
    chp->arr = arr;
    chp->evcnt = evcnt;
    chp->evofs = cofs; // tentative
    chp->kind = hp->kind;
    chp->ctype = 'B';
    chp->rid = rid;
    chp->aid = rp->aid;
    chp->rhop = hp->rhop;
    chp->reserve = (ub1)hp->reserve;
    chp->fare = hp->fare;
    chp->varsda = hp->varsda;
    chp->srdep = hp->srdep & 0xff;
    chp->srarr = hp->srarr & 0xff;
    chp->tripstart = hp->tripstart;
    chp->tripend = hp->tripend;
    chp->lodur = hp->tp.lodur;
    chp->hidur = hp->tp.hidur;
    chp->hop1 = chp->hop2 = hi32;
    infocc(hop == 35214,Emp,"rid %u hop %u",rid,hop);
    cofs += evcnt;
  }

  cumevcnt = cumbevcnt + cumcevcnt;

  hp = hops + hievhop;
  info(0,"hop %u has %u event\as '%s'",hievhop,hievcnt,hp->name);
  info(0,"\ah%lu tentative events",cumevcnt);
  info(0,"\ah%lu+\ah%lu var srda events in \ah%u+\ah%u hops",varbsdalen,varcsdalen,varbsdacnt,varcsdacnt);

  // allocate tentative events, trim after fill
  block *cevmem = &net->cevmem;
  ub8 *cev,*cevents = NULL;
  cevents = net->cevents = mkblock(cevmem,cumevcnt,ub8,Noinit,"cmp events for %u chops",newhopcnt);

  ub8 varsdaofs = 0,varsdalen = varbsdalen + varcsdalen;
  block *sdamem = &net->sdamem;
  ub2 *srdap,*srdap1,*srdalst = mkblock(sdamem,max(varsdalen,1),ub2,Noinit,"var srda list %u+%u",varbsdacnt,varcsdacnt);

  struct chop *chp2,*chp3;
  ub4 chop2,chk;
  ub4 hopndx,h;
  ub4 day,day2,daylen,rdaycnt,rrefdaycnt,refs,rdayrefs,skip,dayskip;
  ub4 e0,e2,len,durofs,tday,tday0,prvarr;
  ub4 cxa = 0,cxb = 0;
  ub4 t;
  ub8 xlen,xlen1,xlen2,xtim1,xtim2,xlim,xdureq,xdura,xdurb,xdurc,refdaycnt;
  ub4 xrlen,xrlen1,xrlen2,xrtim1,xrtim2,xrlim,xrdureq,xrdura,xrdurb,xrdurc;

  ub4 daycnt = 0,dayrefs = 0,daypos;
  ub4 zhevcnt,revcnt = 0,zndx;
  ub8 csum1,csum2,csum3,csum4,timchk;
  ub8 zevcnt = 0;
  ub4 cmpevcnt,cmpevlim = 1024 * 1024;
  ub4 lodur3,hidur3;
  int dif,eqdur,overtake,varsda,evarsda,varsda1;
  ub4 covertakecnt = 0;

  ub4 hoplstlen,hoplstlen2,hoplstmax = 1024 * 16;
  ub4 *hoplst = talloc(hoplstmax,ub4,0,"hoplst",0);

  ub4 rngmin = net->tt1 - gt0 + 60;
  ub8 rnghr = (rngmin / 60) + 2;
  ub4 rngdy = (ub4)(rnghr / 24) + 2;

  // track full days here
  ub4 zdaymlen = hiridhopcnt * rngdy;
  struct refev *zdayp,*zdayp2,*zdaymap = talloc(zdaymlen,struct refev,0,"zdaymap",hiridhopcnt);

  ub4 zlstmax = cmp_maxperm2 + Chainlen;
  ub4 *zlst = talloc(zlstmax,ub4,0,"zlst",zlstmax);
  ub4 zcnt;
  struct eta eta2;
  ub8 totevmem1 = 0,totevmem2 = 0;

  ub4 eventzlo = max(globs.eventzlo,2);

  ub4 lodur,hidur;
  ub4 e,ei1;
  ub4 acc,iacc1,iacc2,iacc3,iac1len,iac2len,iac3len;
  ub4 acc1limcnt = 0,acc2limcnt = 0,acc3limcnt = 0;
  ub4 mapcnt2,totmapcnt2 = 0;
  int prvmapz,eqsda;

static ub4 acc1hist[Iacclen];
static ub4 acc2hist[Iacclen];
static ub4 acc3hist[Iacclen];

static ub2 acc1itab[Iacclen];
static ub2 acc2itab[Iacclen];
static ub2 acc3itab[Iacclen];

  cofs = 0;

  xlen = xlen1 = xlen2 = xtim1 = xtim2 = xlim = xdureq = xdura = xdurb = xdurc = 0;
  refdaycnt = 0;

  dbg = 0;
  ub4 hopdbg = 35214;
  int isair;

  // pass 2
  for (rid = 0; rid < ridcnt; rid++) {
    if (progress(&eta,"pass 2 compound rid %u of %u chops \ah%u",rid,ridcnt,chop - hopcnt)) return 1;

    rp = routes + rid;
    rhopcnt = rp->hopcnt;
    if (rhopcnt == 0) continue;
    error_ge(rhopcnt,Chainlen);
    error_ne(rhopcnt,rp->hihop - rp->lohop + 1);
    rhopcnt2 = rhopcnt * rhopcnt;

    isair = (rp->kind == Airint || rp->kind == Airdom);

    msgprefix(0,"p2 %crid %u",rid,rp->ckind);

    xrlen = xrlen1 = xrlen2 = xrtim1 = xrtim2 = xrlim = xrdureq = xrdura = xrdurb = xrdurc = 0;

    error_lt(chop,hopcnt);
    rp->lochop = lochop = chop;
    lohop = rp->lohop;

    // dbg = (rid == 13);
    nocmpev1 = 0; nocmpev2 = 0;

    info(Iter|V0," hop %u-%u %s",lohop,lohop + rhopcnt,rp->name);

    revofs = 0;
    curtidofs = 0;
    daypos = 0;
    rdayrefs = rdaycnt = 0;

    // base hops
    nsethi(port2rport,portcnt);
    rportcnt = 0;
    for (hop = lohop; hop <= rp->hihop; hop++) {
      infocc(dbg,0,"hop %u",hop);
      chp1 = chops + hop;
      thp1 = thops + hop;
      error_ne(chp1->rid,rid);

      dep = chp1->dep; arr = chp1->arr;
      error_eq(dep,arr);
      error_ge(dep,portcnt);
      error_ge(arr,portcnt);

      if (port2rport[dep] == hi32) {
        port2rport[dep] = rportcnt;
        error_ge(rportcnt,hiportlen);
        rport2port[rportcnt++] = dep;
      }

      if (port2rport[arr] == hi32) {
        port2rport[arr] = rportcnt;
        error_ge(rportcnt,hiportlen);
        rport2port[rportcnt++] = arr;
      }
      thp1->tidpos = 0;
      thp1->tidofs = 0;
    }

    if (rportcnt == 0) {
      warn(0,"no ridports for %u hops",rp->hopcnt);
      continue;
    }
    error_gt(rportcnt,hiportlen,0);
    rportcnt = min(rportcnt,hiportlen);
    error_ovf(rportcnt,ub2);
    rport2 = rportcnt * rportcnt;
    nsethi(duphops,rhopcnt2);

    // infocc(dbg || rid == 338,0,"%u hops %s",rp->hopcnt,rp->loop ? "loop" : "");

    newcnt = 0;
    warnlim = 1;
    for (chain = rp->lochain; docompound && chain < rp->lochain + rp->chaincnt; chain++) {
      cp = chains + chain;
      error_ne(cp->rid,rid);

      infocc(dbg,Iter|V0,"chain %u",chain);

      cnt = cp->hopcnt;

      // infocc(dbg || rid == 1,Iter|V0,"chain %u len %u chop %u r.tid %u",chain,cnt,chop,cp->rtid);
      error_gt(cnt,rp->hopcnt,chain);
      if (cnt < 2) continue;

      // dbg = (rid == 120 && chain == 3790);
      // infocc(dbg,Notty,"rid %u tid %u len %u",rid,chain,cnt);

      pchlen = 0; cdist = 0;
      for (ci = 0; ci < cnt; ci++) {
        cnhp = chainhops + cp->hopofs + ci;
        error_ne(chain,cnhp->chain);
        hop = cnhp->hop;
        error_ge(hop,hopcnt);
        chp1 = chops + hop;
        error_ne(chp1->rid,rid);

        dep = chp1->dep;
        arr = chp1->arr;

        if (dep == arr) return error(0,"hop %u dep %u = arr",hop,dep);

        // infocc(chain == 113 || chain == 21873,0,"ci %u idx %u hop %u tid %u da %u,%u %s",ci,pchlen,hop,chain,dep,arr,hp->name);

        pdep = ports + dep;
        parr = ports + arr;

        rdep = port2rport[dep];
        rarr = port2rport[arr];
        error_ge_cc(rdep,rportcnt,"dep %u",dep);
        error_ge(rarr,rportcnt);

        for (ci2 = 0; ci2 < pchlen; ci2++) {
          hop2 = pchain[ci2];
          if (hop != hop2) continue;
          error(Exit,"rid %u chain %u hop %u pos %u equals pos %u %s to %s",rid,chain,hop,pchlen,ci2,pdep->name,parr->name);
        }

        error_lt(cnhp->tarr,cnhp->tdep);

        dist = hopdist[hop];
        pchain[pchlen] = hop;
        pdeps[pchlen] = rdep;
        parrs[pchlen] = rarr;
        pdist[pchlen] = cdist;
        ptdep[pchlen] = cnhp->tdep;
        ptarr[pchlen] = cnhp->tarr;

        psrda[pchlen] = cnhp->srda;
        srdep1 = (cnhp->srda >> 8) & 0xff;
        srarr1 = cnhp->srda & 0xff;
        if (chp1->varsda == 0) {
          error_ne(srdep1,chp1->srdep);
          error_ne(srarr1,chp1->srarr);
        }
        ptarrseq[pchlen] = cnhp->seq;
        cdist += max(dist,1);
        pchlen++;
        if (pchlen == maxperm) break;
        error_gt(pchlen,cnt,chain);
      }
      if (pchlen < 2) continue;

      pchaincnt++;
      cumchainlen += pchlen;

      // generate all not yet existing compounds
      // note that some chains visit ports more than once
      cmpcnt = 0;
      cnhp = chainhops + cp->hopofs;

      for (ci1 = 0; ci1 < pchlen - 1 && cmpcnt < cmp_maxperm2; ci1++) {

        dep1 = pdeps[ci1];
        hop1 = pchain[ci1];
        rhop1 = hop1 - lohop;

        infocc(chain == rp->lochain,Iter|V0,"chop %u ci1 %u of %u dep %u",chop,ci1,pchlen,dep);

        for (ci2 = ci1 + 1; ci2 < pchlen && cmpcnt < cmp_maxperm2; ci2++) {

          arr2 = parrs[ci2];

          hop2 = pchain[ci2];

          if (dep1 == arr2) {
            // infocc(cp->rtid == 57510 || chop == 23665 || rid == 1,Iter|V0,"chop %u rid %u r.tid %u.%u seq %u ci %u,%u hop %u,%u",
            //  chop,rid,cp->rtid,chain,ptarrseq[ci2],ci1,ci2,hop1,hop2);
            continue;
          }

          rhop2 = hop2 - lohop;
          rhop12 = rhop1 * rhopcnt + rhop2;
          error_ge(rhop12,rhopcnt2);

          deparr = dep1 * rportcnt + arr2;  // filter redundant options in looping trips
          dupda = dupdas[deparr];
          if (dupda != hi32) {
            for (ci3 = 0; ci3 < ci2; ci3++) {
              if (parrs[ci3] == arr2) break;
            }
            if (ci3 < ci2) continue;
          } else dupdas[deparr] = ci1 << 16 | ci2;

          prvchop = duphops[rhop12];

          chp1 = chops + hop1;
          chp2 = chops + hop2;
          error_ne(chp1->rid,rid);
          error_ne(chp2->rid,rid);

          error_eq(hop1,hop2);

          // infocc(chain == 21873 && hop1 == 7642 && hop2 == 7644,Iter,"chop %u ci %u,%u hop %u,%u tid %u",chop,ci1,ci2,hop1,hop2,chain);
          // infocc(chop == 135897,Iter,"chop %u ci %u,%u hop %u,%u tid %u",chop,ci1,ci2,hop1,hop2,chain);

          tdep1 = ptdep[ci1];
          tarr2 = ptarr[ci2];

          error_lt(tarr2,tdep1);
          dur = tarr2 - tdep1;
          error_lt(dur,chops[hop1].lodur);
          if (dur >= Durlim) {
            warn(0,"chop %u.%u dur %u above lim %u",hop1,hop2,dur,Durlim);
            dur = Durlim - 1;
          }
          error_lt(ptarrseq[ci2],ptarrseq[ci1]);

          if (prvchop != hi32) {  // existing: accumulate and range duration
            curchop = prvchop;
            error_ge(curchop,chop);
            error_ge(curchop,newhopcnt);
            error_lt(curchop,hopcnt);
            chp = chops + curchop;
            thp = thops + curchop;

            srda = psrda[ci2];

            srdep2 = srda >> 8;
            srarr2 = srda & 0xff;
            if (chp2->varsda == 0) {
              error_ne(srdep2,chp2->srdep);
              error_ne_cc(srarr2,chp2->srarr,"hop %u",hop2);
            }

            // infocc(curchop == 21861 || rid == 1,V0,"chop %u rid %u r.tid %u.%u td %u ta %u seq %u ci %u,%u hop %u,%u",
            //  curchop,rid,cp->rtid,chain,tdep1,tarr2,ptarrseq[ci2],ci1,ci2,hop1,hop2);

            chp->lodur = min(chp->lodur,dur);
            chp->hidur = max(chp->hidur,dur);

            tidofs = thp->tidofs;
          } else {
            if (chop >= newhopcnt) {
              warn(0,"limiting %u,%u compound to %u hops, len %u",ci1,ci2,chop - rp->lochop,pchlen);
              break;
            }
            thp = thops + chop;

            thp->tidofs = tidofs = curtidofs;
            vrb0(Iter,"hop %u tidofs %u",chop,curtidofs);
            curtidofs += rp->chaincnt;
            curchop = chop;
          }

          // prepare compound
          dist1 = pdist[ci1];
          dist2 = pdist[ci2];

          srdep1 = psrda[ci1] >> 8;
          srarr2 = psrda[ci2] & 0xff;

          srda = (srdep1 << 8) | srarr2;

          // store chain info for subsequent event fill

          chp = chops + curchop;
          thp = thops + curchop;
          error_ge_cc(tidofs,hoptidlen,"%u cmp hops",newcnt + cmpcnt);

          tidpos = thp->tidpos;

          // infocc(curchop == 21858 && tidpos == 113,0,"ci %u,%u hop %u,%u chop %u d.tid %u.%u td %u,%u ta %u,%u seq %u,%u ofs %u pos %u",
          //  ci1,ci2,hop1,hop2,curchop,chain - rp->lochain,chain,tdep1,ptdep[ci2],ptarr[ci1],tarr2,ptarrseq[ci1],ptarrseq[ci2],tidofs,tidpos);

          dtid = chain - rp->lochain;
          error_gt_cc(tidpos,dtid,"hop %u of %u",curchop,chop);

          error_ge_cc(tidpos,rp->chaincnt,"hop %u of %u",prvchop,chop);
          error_ge(tidofs + tidpos,hoptidlen);
          pos = tidofs + tidpos;
          if (pos >= hoptidlen) return error(0,"pos %u out of bound %u",pos,hoptidlen);
          hopdtidlst[pos] = dtid;
          hopstlst[pos] = ((ub8)srda << 32) | dur;
          hop12lst[pos] = ((ub8)hop1 << 32) | hop2;
          hophlst[pos] = curchop;

          thp->tidpos = tidpos + 1;

//          info(0,"hop %u = %u,%u tidpos %u chain %u prv %u",curchop,hop1,hop2,tidpos,chain,prvchop);
          infocc(curchop == 21858 && tidpos == 113,0,"hop %u = %u,%u tidpos %u chain %u",curchop,hop1,hop2,tidpos,chain - rp->lochain);

          infocc(dist2 == 0,0,"chop %u dist %u+%u",chop,dist1,dist2);

          if (prvchop != hi32) continue;

          duphops[rhop12] = chop;

          // generate compound
          chp->rid = rid;
          chp->hop1 = hop1;
          chp->hop2 = hop2;

          chp->ctype = 'C';

          // infocc(chop <= 21860,0,"hop %u = %u,%u tidpos %u chain %u",curchop,hop1,hop2,tidpos,chain);

          dep = rport2port[dep1];
          arr = rport2port[arr2];
          chp->dep = dep;
          chp->arr = arr;
          portsbyhop[chop * 2] = dep;
          portsbyhop[chop * 2 + 1] = arr;

          chp1 = chops + hop1;
          chp2 = chops + hop2;
          error_ne(chp1->rid,rid);
          error_ne(chp2->rid,rid);
          if (chp1->reserve) {
            cumcfevcnt += chp1->evcnt;
            cumfhops++;
          }

          chp->srdep = chp1->srdep;
          chp->srarr = chp2->srarr;

          error_lt(hop1,lohop);
          error_lt(hop2,lohop);
          error_ge(rhop1,rp->hopcnt);
          error_ge(rhop2,rp->hopcnt);

          crp = chainrhops + cp->rhopofs;

          error_lt(dist2,dist1); // todo ?

          dist = dist2 - dist1 + hopdist[hop2];

          pdep = ports + dep;
          parr = ports + arr;

          dirdist = fgeodist(pdep,parr,0);
          hopdist[chop] = max(dist,dirdist);

          if (tarr2 < tdep1) {
            return error(0,"rid %u tdep %u before tarr %u %s to %s",rid,tdep1,tarr2,pdep->iname,parr->name);
          }

          idx1 = crp[rhop1];
          idx2 = crp[rhop2];
          error_eq(idx1,hi16);
          error_eq(idx2,hi16);
          error_ge(idx1,cnt);
          error_ge(idx2,cnt);

          error_ne_cc(cnhp[idx1].tdep,tdep1,"r.tid %u.%u seq %u vs %u",cp->rtid,chain,cnhp[idx2].seq,ptarrseq[ci2]);

          error_ne_cc(cnhp[idx2].tarr,tarr2,"r.tid %u.%u seq %u vs %u",cp->rtid,chain,cnhp[idx2].seq,ptarrseq[ci2]);

          if (tarr2 >= tdep1) midur = tarr2 - tdep1;
          else {
            error(Exit,"r.tid %u.%u td %u ta %u seq %u,%u ci %u,%u",cp->rtid,chain,tdep1,tarr2,cnhp[idx1].seq,ptarrseq[ci2],ci1,ci2);
            midur = hi32;
          }

          error_lt(midur,chp1->lodur);

#if 0
          infocc(chop == 21861,0,"+++ chop %u rid %u r.tid %u.%u len %u td %u ta %u seq %u,%u ci %u,%u rh %u,%u hop %u,%u",
            chop,rid,cp->rtid,chain,cnt,tdep1,tarr2,cnhp[idx1].seq,cnhp[idx2].seq,ci1,ci2,rhop1,rhop2,hop1,hop2);
          infocc(chop == 21861,0,"+++ dur1 %u dur2 %u",chops[hop1].lodur,chops[hop2].lodur);
#endif

          // first entry
          chp->lodur = chp->hidur = midur;

          // set tmp event store
          error_ge(chop,newhopcnt);

          // infocc(dbg,Notty|Noiter,"chop %u = %u-%u %u-%u td %u ta %u %s - %s",chop,hop1,hop2,dep,arr,tdep1,tarr2,pdep->name,parr->name);
          chop++;
          cmpcnt++;
          error_ge(cmpcnt,cmp_maxperm2);
        } // each c2
        // if (chop >= newhopcnt) break;
      } // each c1
      // if (chop >= newhopcnt) break;
      newcnt += cmpcnt;
    } // each chain

    error_gt(chop,newhopcnt,0);
    net->chopcnt = chop;

    info(V0,"%u cmp hops",newcnt);

    rp->chopcnt = chop - lochop;
    // error_ge(newcnt,cmp_maxperm2);

    // assemble temp events per rid
    // compress and append to cevents
    // do not compress hops with low max events per day
    revcnt = 0;
    zndx = 0;
    acclimcnt = 0;

    // base hops
    for (hop = lohop; hop <= rp->hihop; hop++) {

      msgprefix(0,"rid %u hop %u",rid,hop);
      chp = chops + hop;
      thp = thops + hop;
      error_nz(thp->init1,hop);
      thp->init1 = 1;
      hp = hops + hop;
      bev = bevents + hp->tp.evofs;
      if (hop == 0) error_nz(hp->tp.evofs,0);
      error_ne_cc(chp->rid,rid,"lo.hop %u.%u",lohop,hop);
//      chp->chaincnt = rp->chaincnt;
//      error_z(chp->chaincnt);
      bevcnt = chp->evcnt;
      error_ge(zndx,zlstmax);
      zlst[zndx++] = hop;

      error_ge(revofs,ridevcnt);
      error_gt(revofs + bevcnt,ridevcnt,hop);
      chp->evofs = revofs;
      // infocc(hop == 35214,Emp,"hop %u ofs %u",hop,revofs);
      rev = ridevents + revofs;
      rei = acc1ei = acc2ei = acc3ei = 0;
      prvt = (ub4)*bev;
      acc1rt = prvt + Acc1iv;
      acc2rt = prvt + Acc2iv;
      acc3rt = prvt + Acc3iv;
      chp->t0 = prvt + gt0;
      srdap = srdalst + varsdaofs;
      chp->sdaofs = varsdaofs;
      varsda = chp->varsda;
      lodur = chp->lodur;
      hidur = chp->hidur;
      // infocc(hop == 35214,Emp,"hop %u dur %u-%u",hop,lodur,hidur);

      for (bei = 0; bei < bevcnt; bei++) {
        bx = bev[bei * 2];

        rt = (ub4)bx;
        error_lt(rt,prvt);
        if (rt >= Timlim) return hopmsg(Error,0,hop,"relative time %u exceeds %u",rt,Timlim);

        if (acc1ei == 0) {
          if (rt < acc1rt) {
            thp->acc1ei = rei;
          } else acc1ei = rei;
        }
        if (acc2ei == 0) {
          if (rt < acc2rt) {
            thp->acc2ei = rei;
          } else acc2ei = rei;
        }
        if (acc3ei == 0) {
          if (rt < acc3rt) {
            thp->acc3ei = rei;
          } else acc3ei = rei;
        }

        prvt = rt;

        dur = (ub4)(bx >> 32);
        error_lt(dur,lodur);
        error_gt(dur,hidur,bei);
        bx1 = bev[bei * 2 + 1];
        dtid = bx1 & hi16;
        chk = (bx1 >> 16) & hi16;
        // infocc(hop == 0 && bei == 0,0,"x %lx at %p",bx1,bev);
        error_ne_cc(chk,hop,"ndx %u t %u dur %u dtid %u",bei,rt,dur,dtid);
        error_ge(dtid,rp->chaincnt);

        tid = dtid + rp->lochain;

        if (dtid > Dtidlim) {
          if (isair) return hopmsg(Error,0,hop,"dtid %u above %u",dtid,Dtidlim);
          else dtid = Dtidlim;
        }

        srda = (ub2)(bx1 >> 32);

        // infocc( (hop == 7642 || hop == 7644) && tid == 21873,0,"hop %u ev %u tid %u t \ad%u dur %u",hop,bei,tid,rt + gt0,dur);
        // infocc(bei < 5 && (hop == 61 || hop == 62),Emp,"hop %u ev %u srda %x",hop,bei,srda);

        if (dur >= Durlim) {
          warn(0,"hop %u dur %u above lim %u",hop,dur,Durlim);
          dur = Durlim - 1;
        }

        rx = ((ub8)dtid << Dtidshift) | ((ub8)dur << Durshift) | rt;
        rx |= (ub8)(hop & 0xff) << Accshift;
        rev[rei] = rx;
        if (varsda) srdap[rei] = (ub2)srda;
        rei++;
      } // each event

      if (bevcnt > Acclim) {
        hopmsg(Info,Iter,hop,"\ah%u evs",bevcnt);
        acclimcnt++;
      }

      //infocc(hop == 35214,Emp,"hop %u evs %u",hop,rei);
      revcnt += bevcnt;
      revofs += bevcnt;
      if (varsda) {
        varsdaofs += bevcnt;
        error_gt(varsdaofs,varsdalen,hop);
      }

    } // each base hop
    warn(CC0,"\ah%u of \ah%u hops exceeding acc limit",acclimcnt,rp->hihop - lohop);

    ub4 eqdurcnt = 0,ltdurcnt = 0,ltdurcnt1 = 0,ltdurcnt2 = 0,gtdurcnt = 0,nocevcnt = 0;

    // cmp hops
    for (c1 = lochop; c1 < chop; c1++) {
      msgprefix(0,"rid %u chop %u",rid,c1);
      if (isair) fatal(0,"cmp hop %u/%u on air mode",c1,chop);

      chp = chops + c1;
      thp = thops + c1;
      error_ne_cc(chp->rid,rid,"lo.hop %u.%u",lochop,c1);
      hop1 = chp->hop1;
      hop2 = chp->hop2;
      hp1 = NULL;
      hp2 = NULL;

      chp1 = chops + hop1;
      chp2 = chops + hop2;
      thp1 = thops + hop1;

      error_ne(chp1->rid,rid);
      rev1 = ridevents + chp1->evofs;
      evcnt1 = chp1->evcnt;
      evcnt2 = chp2->evcnt;
      varsda1 = chp1->varsda;
      evarsda = (varsda1 || chp2->varsda); // tentative
      varsda = 0;
      srdap = srdalst + varsdaofs;
      srdap1 = srdalst + chp1->sdaofs;
      chp->sdaofs = varsdaofs;
      error_gt(varsdaofs,varsdalen,c1);
      error_gt_cc(varsdaofs + evcnt1,varsdalen,"chop %u evs %u",c1,evcnt1);

      msgprefix(0,"p2 rid %u chop %u",rid,c1);

      if (zndx < zlstmax) zlst[zndx++] = c1;
      else return error(0,"zndx %u above max %u",zndx,zlstmax);
      chp->evofs = revofs;
      error_ge(revofs,ridevcnt);
      error_ge(revofs + evcnt1,ridevcnt);
      // infocc(rid == 4,0,"chop %u revofs %u",c1,revofs2);
      rev = ridevents + revofs;
      rei = 0;

      tidofs1 = thp->tidofs;
      error_ge(tidofs1,hoptidlen);

      tidlen1 = thp->tidpos;
      if (tidlen1 == 0) {
        warn(Emp,"no tid for hop %u",c1);
        nocevcnt++;
        continue;
      }

      error_gt(tidlen1,rp->chaincnt,0);
      error_ge(tidofs1 + tidlen1,hoptidlen);

      hdp1 = hopdtidlst + tidofs1;
      hsp1 = hopstlst + tidofs1;
      h12p = hop12lst + tidofs1;

      hhp = hophlst + tidofs1;

      error_ne(hhp[0],c1);

      xhop1 = (ub4)(h12p[0] >> 32);
      xhop2 = h12p[0] & hi32;

      error_ne(xhop1,hop1);
      error_ne(xhop2,hop2);

      prvt = rev1[0] & Timlim;
      chp->t0 = prvt + gt0;

      acc1ei = thp1->acc1ei;
      acc2ei = thp1->acc2ei;
      acc3ei = thp1->acc3ei;

      acc1rt = prvt + Acc1iv;
      acc2rt = prvt + Acc2iv;
      acc3rt = prvt + Acc3iv;

      overtake = 0;
      prvarr = 0;
      lodur = hi32;
      hidur = 0;

      for (ei1 = 0; ei1 < evcnt1; ei1++) {
        rx = rev1[ei1];

        rt = rx & Timlim;

        acc = (rx >> Accshift) & 0xff;
        error_ne(acc,hop1 & 0xff);
        error_lt_cc(rt,prvt,"hop %u acc %u ev %u",hop1,acc,ei1);

        dur1 = (rx >> Durshift) & Durlim;
        dtid = (rx >> Dtidshift) & Dtidlim;

        infocc(hop1 == 7642 && hop2 == 7644 && dtid == 2,V0,"hop %u,%u ev %u tid %u t \ad%u dur %u",hop1,hop2,ei1,dtid,rt + gt0,dur1);

        // hop 1
        if (varsda1) {
          srda1 = srdap1[ei1];
          srdep1 = srda1 >> 8;
          srarr1 = srda1 & 0xff;
          infocc(hop1 == 61,V0,"ei %u srda %x",ei1,srda1);
        } else {
          srdep1 = chp1->srdep;
          srarr1 = chp1->srarr;
          srda1 = (srdep1 << 8) | srarr1;
          infocc(hop1 == 61,V0,"ei %u srda %x",ei1,srda1);
        }

        nocmpev = 0;
        ndx1 = bsearch4(hdp1,tidlen1,dtid,FLN,"tid");
        if (ndx1 == tidlen1) {
          nocmpev1++;
          // infocc(hop1 == 35214 || hop2 == 35214,V0,"hop %u,%u no evs from %u,%u",hop1,hop2,evcnt1,evcnt2);
          vrb0(Iter,"hop %u,%u no ev from %u,%u",hop1,hop2,evcnt1,evcnt2);
          nocmpev = 1;
        } else if (hdp1[ndx1] != dtid) {
          nocmpev2++;
          // hopmsg(Info,0,c1,"hop %u,%u no ev from %u,%u",hop1,hop2,evcnt1,evcnt2);
          nocmpev = 1;
        }
        if (nocmpev) {
          if (ei1 < acc1ei && acc1ei) acc1ei--;
          else if (ei1 == acc1ei && acc1ei) acc1ei--;
          prvt = rt;
          continue;
        }
        prvt = rt;

        rsx = hsp1[ndx1];
        srarr2 = (ub2)(rsx >> 32) & 0xff;
        if (chp2->varsda == 0) { error_ne(srarr2,chp2->srarr); }
        dur = rsx & Durlim;
        error_lt(dur,chp1->lodur + chp2->lodur);
        // error_gt_cc(dur,chp1->hidur + chp2->hidur,"%u+%u",chp1->hidur,chp2->hidur);
        lodur = min(lodur,dur);
        hidur = max(hidur,dur);

        infocc(hop1 == 61,V0,"ei %u srda %u,%u",ei1,srdep1,srarr2);
        if (varsda == 0 && rei && (srdep1 != prvsrdep1 || srarr2 != prvsrarr2)) {
          varsda = 1;
          if (evarsda == 0) return error(0,"chop %u=%u,%u ei %u varsda %u,%u vs %u,%u",c1,hop1,hop2,ei1,srdep1,srarr2,prvsrdep1,prvsrarr2);
        }
        prvsrdep1 = srdep1;
        prvsrarr2 = srarr2;
        infocc(hop1 == 61,V0,"ei %u srda %u,%u",ei1,srdep1,srarr2);

        xhop1 = (ub4)(h12p[ndx1] >> 32);
        xhop2 = h12p[ndx1] & hi32;

        error_ne_cc(hhp[ndx1],c1,"ndx %u len %u",ndx1,tidlen1);

        error_ne(xhop1,hop1);
        error_ne_cc(xhop2,hop2,"ofs %u ndx %u len %u dtid %u",tidofs1,ndx1,tidlen1,dtid);

// todo
        if (dur == dur1) {
          infocc(dbg,Iter,"dur %u = dur1 %u dtid %u at ndx %u ofs %u lhdur %u-%u,%u-%u sa %u",
            dur,dur1,dtid,ndx1,tidofs1,chp1->lodur,chp1->hidur,chp2->lodur,chp2->hidur,srarr1);
          eqdurcnt++;
        } else if (dur + 1 == dur1) {
          info(Iter|V0,"hop %u,%u dur %u dur1 %u ev %u dtid %u lhdur %u-%u,%u-%u sa %u",
            hop1,hop2,dur,dur1,ei1,dtid,chp1->lodur,chp1->hidur,chp2->lodur,chp2->hidur,srarr1);
          ltdurcnt1++;
        } else if (dur + 2 == dur1) {
          info(Iter|V0,"dur %u dur1 %u dtid %u at ndx %u ofs %u lhdur %u-%u,%u-%u sa %u",
            dur,dur1,dtid,ndx1,tidofs1,chp1->lodur,chp1->hidur,chp2->lodur,chp2->hidur,srarr1);
          ltdurcnt2++;
        } else if (dur < dur1) {
          info(Iter|V0,"dur %u < dur1 %u dtid %u at ndx %u ofs %u lhdur %u-%u,%u-%u sa %u",
            dur,dur1,dtid,ndx1,tidofs1,chp1->lodur,chp1->hidur,chp2->lodur,chp2->hidur,srarr1);
          ltdurcnt++;
        } else gtdurcnt++;

        if (rt + dur < prvarr) overtake = 1;
        prvarr = rt + dur;
        rx = ((ub8)dtid << Dtidshift) | ((ub8)dur << Durshift) | rt;
        rx |= (ub8)c1 << Accshift;
        rev[rei] = rx;
        if (evarsda) {
          srda = (srdep1 << 8) | srarr2;
          srdap[rei] = (ub2)srda;
        }
        rei++;
        error_gt(rei,evcnt1,c1);
      } // each event

      revcnt += rei;
      revofs += rei;

      chp->lodur = lodur;
      chp->hidur = hidur;

      thp->acc1ei = acc1ei;
      thp->acc2ei = acc2ei;
      thp->acc3ei = acc3ei;

      thp->init1 = 1;

      chp->kind = chp1->kind;

      chp->srdep = chp1->srdep;
      chp->srarr = chp2->srarr;
      chp->varsda = (ub2)varsda;
      if (varsda) {
        varsdaofs += rei;
        error_gt(varsdaofs,varsdalen,c1);
      }

      if (overtake) { chp->overtake = 1; covertakecnt++; }

      chp->evcnt = rei;
      if(rei == 0) {
        info(Iter,"chop %u no evs from %u",c1,evcnt1);
        nocevcnt++;
      }
      // infocc(hop1 == hopdbg || hop2 == hopdbg,Emp,"hop %u,%u evs %u from %u,%u",hop1,hop2,rei,evcnt1,evcnt2);
    } // each new cmp hop

    msgprefix(0,"rid %u",rid);

    info(CC0|Emp,"%u of %u chops with no events",nocevcnt,chop - lochop);
    if (nocevcnt * 2 > chop - lochop) warn(0,"%u chops with no events",nocevcnt);

    error_ge(sumnocevcnt,hi32 - nocevcnt);
    sumnocevcnt += nocevcnt;

    zcnt = zndx;
    error_z(zcnt,0);

    info(CC0,"%u of %u ltdurs: 1.%u 2.%u n.%u",ltdurcnt2 + ltdurcnt1 + ltdurcnt,gtdurcnt + eqdurcnt,ltdurcnt1,ltdurcnt2,ltdurcnt);
    info(CC0|V0,"%u of %u eqdurs",eqdurcnt, eqdurcnt + gtdurcnt);
    info(CC0|Iter|V0,"\ah%lu of \ah%lu variable sda",varsdaofs,varsdalen);

    // generate zevents: refer to preceding 24-hour period if equal except tid
    // for each preceding day,check length, then checksum, then content

    rrefdaycnt = 0;

    daycnt = 0;
    dayrefs = 0;
    dayskip = 0;

   info(V0,"zcnt %u",zcnt);

   for (zndx = 0; do_compress && zndx < zcnt; zndx++) {
    zchop = zlst[zndx];

     mapcnt2 = 0;
     prvmapz = 0;

    dbg = (rid == 0 && zchop == 0);

    if (progress(&eta2,"-compress events item %u of %u days %u refs %u",zndx,zcnt,daycnt,rrefdaycnt)) return 1;

    chp = chops + zchop;
    error_ne(chp->rid,rid);

    if (chp->kind == Taxi || chp->kind == Airdom) continue;

    cevcnt = chp->evcnt;
    if (cevcnt < 16) continue;

    eqsda = (chp->varsda == 0);

    msgprefix(0,"p2 rid %u hop %u ",rid,zchop);

    if (zchop < hopcnt) hp1 = hops + zchop;
    else hp1 = hops + chp->hop1;

    refs = 0;
    zhevcnt = 0;
    skip = 0;

    // create list of hops to compare: fist self, then base hops in same rid, then cmp
    rid = chp->rid;
    rp = routes + rid;
    rhopcnt = rp->hopcnt;

    hoplstlen = 1;
    hoplst[0] = zchop;
    for (h = lohop; h <= rp->hihop && hoplstlen < hoplstmax; h++) {
      error_ge(h,hopcnt);
      if (h == zchop) continue;
      chp2 = chops + h;
      error_ne(chp2->rid,rid);
      if (chp2->daycnt == 0 || chp2->dayhilen < 8) continue;
      hoplst[hoplstlen++] = h;
    }

    // add derived compounds
    hoplstlen2 = hoplstlen;
    for (hopndx = 0; hopndx < hoplstlen2; hopndx++) {
      h = hoplst[hopndx];
      if (h >= hopcnt || zchop < lochop) continue;

      chp2 = chops + h;
      error_ne(chp2->rid,rid);
      if (chp2->chopcnt == 0) continue;

      for (chop2 = chp2->choplo; chop2 <= chp2->chophi && hoplstlen < hoplstmax; chop2++) {
        if (chop2 >= zchop) continue;
        chp3 = chops + chop2;
        if (chp3->rid != rid) continue;
        if (chp3->daycnt == 0 || chp3->dayhilen < 8) continue;
        hoplst[hoplstlen++] = chop2;
      }
    }
    infocc(hoplstlen != hoplstlen2,CC0|Iter,"hoplst %u from %u",hoplstlen,hoplstlen2);
    // infocc(dbg,0,"hoplst %u from %u",hoplstlen,hoplstlen2);

    error_ge(daypos,zdaymlen);
    info(V0,"hop %u daypos %u",zchop,daypos);
    chp->daypos = daypos;

    pdep = ports + portsbyhop[zchop * 2];
    parr = ports + portsbyhop[zchop * 2 + 1];

    lodur = chp->lodur;
    hidur = chp->hidur;
    eqdur = (lodur == hidur);

    revofs = (ub4)chp->evofs;
    if (revofs == hi32) return error(0,"chop %u no revent offset",zchop);
    infocc(rid == 13,V0,"hop %u revofs %u",zchop,revofs);

    rev = ridevents + revofs;

    day = daylen = 0;
    csum1 = csum2 = csum3 = csum4 = 0;

    tday0 = prvt = rev[0] & Timlim;
//    tday0 -= min(60,gt0);

    e = e0 = 0;

    // infocc(zchop == 21,0,"evs %u dur %u-%u base %u,%u \ad%u %s %s",cevcnt,lodur,hidur,chp->hop1,chp->hop2,tday0 + net->t0,pdep->name,parr->name);

    while (e < cevcnt) {
      rx = rev[e];

      t = rx & Timlim;
      error_lt_cc(t,prvt,"revofs %u ev %u of %u",revofs,e,cevcnt);
      prvt = t;

      dur = (ub4)(rx >> Durshift);

      tday = t - tday0;

      len = e - e0;

      if (tday < 24 * 60) {

      // info(0,"t %u bt %u days %u %u",t,bt,day,nday);
        csum1 = (csum1 + tday) & hi32;
        csum2 = (csum2 + csum1) & hi32;

        e++;
        if (e < cevcnt) continue;
        else break;
      } else if (len < eventzlo) {
        infocc(zchop == 420,0,"day %u len %u t \ad%u",day,len,t + net->t0);
        skip++;
        zevcnt += len;
        zhevcnt += len;
        error_ge_cc(day,rngdy,"hop %u evs %u day %u len %u t \ad%u",zchop,cevcnt,day,len,t + net->t0);
        day++;
        e0 = e;
        tday0 += 24 * 60;
        if (len && prvmapz) mapcnt2++;
        prvmapz = 0;
        if (e == cevcnt) break;
        continue;
      }
      error_z(len,cevcnt);

      // close current day
      timchk = csum1 | (csum2 << 32);

      csum1 = csum2 = 0;
      cmpevcnt = 0;

      zdayp = zdayp2 = zdaymap + daypos;

      infocc(dbg || zchop == 420,V0,"day %u len %u t \ad%u",day,len,t + net->t0);

      // for each base hop on same route for each derived compound for each day
      dif = 1;
      day2 = 0;
      for (hopndx = 0; eqsda && hopndx < hoplstlen; hopndx++) {
        h = hoplst[hopndx];
        chp3 = chops + h;
        error_ne(chp3->rid,rid);
        if (chp3->daycnt == 0 || len < chp3->daylolen || len > chp3->dayhilen) {
          continue;
        }

        error_ge(h,chop);
        revofsr = (ub4)chp3->evofs;
        error_eq_cc(revofsr,hi32,"hop %u",h);
        // infocc(rid == 4,0,"hop %u revofs %u",h,revofsr);

        revr = ridevents + revofsr;

        // for each day
        for (day2 = 0; day2 < chp3->daycnt; day2++) {
          error_ge(chp3->daypos,zdaymlen);
          error_ge(chp3->daypos + day2,zdaymlen);
          zdayp2 = zdaymap + chp3->daypos + day2;
          error_ne_cc(zdayp2->hop,h,"pos %u+%u cnt %u len %u tim %lx",chp3->daypos,chp3->daycnt,day2,zdayp2->len,zdayp2->timchk);

          error_ge(revofsr + zdayp2->pos,ridevcnt);
          error_ge(revofsr + zdayp2->pos + len,ridevcnt);
          error_ge(revofs + e0,ridevcnt);
          error_ge(revofs + e0 + len,ridevcnt);

//          infocc(dbg,Noiter," chk hop %u day %u",h,day2);
          if (zdayp2->len != len) {
            // infocc(dbg,Noiter," dif hop %u day %u len %u",h,day2,zdayp2->len);
            xrlen++;
            if (zdayp2->len + 1 == len || zdayp2->len == len + 1) xrlen1++;
            if (zdayp2->len + 2 == len || zdayp2->len == len + 2) xrlen2++;
            continue;
          }

          if (zdayp2->timchk != timchk) {
            // infocc(dbg,Noiter," dif hop %u day %u tim %lu",h,day2,timchk);
            xrtim1++;
            continue;
          }

          /* check non-constant time dif */
          for (e2 = 0; e2 < len; e2++) {
            cxa = (ub4)(rev[e0 + e2] & Timlim);
            cxb = (ub4)(revr[zdayp2->pos + e2] & Timlim);
            if (cxa -tday0 != cxb - zdayp2->tday0) break;
          }
          if (e2 < len) {
            info(0,"\ad%u vs \ad%u dif %u,%u",cxa,cxb,cxa -tday0,cxb - zdayp2->tday0);
            xrtim2++;
            continue;
          }

          cmpevcnt += len;
          if (cmpevcnt > cmpevlim) {
            // infocc(dbg,Noiter," dif hop %u day %u lim %u",h,day2,cmpevcnt);
            xrlim++;
            break;
          }

          // ignore tid

          // compare dur
          lodur3 = chp3->lodur;
          hidur3 = chp3->hidur;

          if (eqdur && lodur3 == hidur3) {
            dif = 0;
          } else if (lodur3 == lodur && hidur3 == hidur) {
            for (e2 = 0; e2 < len; e2++) {
              cxa = (ub4)(rev[e0 + e2] >> Durshift) & Durlim;
              cxb = (ub4)(revr[zdayp2->pos + e2] >> Durshift) & Durlim;
              if (cxa != cxb) break;
//              else if (cxa != cxb + 1 && cxb != cxa + 1) break;
            }
            dif = (e2 < len);
            if (dif) xrdureq++;
          } else if (lodur3 < lodur && hidur3 < hidur && (lodur - lodur3 == hidur - hidur3) ) {
            durofs = lodur - lodur3;
            for (e2 = 0; e2 < len; e2++) {
              cxa = (ub4)(rev[e2 + e0] >> Durshift) & Durlim;
              cxb = (ub4)(revr[e2 + zdayp2->pos] >> Durshift) & Durlim;
              if (cxa + durofs != cxb) break;
//              else if (cxa + durofs != cxb + 1 && cxb != cxa + durofs + 1) break;
            }
            dif = (e2 < len);
            if (dif) xrdura++;
          } else if (lodur3 > lodur && hidur3 > hidur && (lodur3 - lodur == hidur3 - hidur) ) {
            durofs = lodur3 - lodur;
            for (e2 = 0; e2 < len; e2++) {
              cxa = (ub4)(rev[e2 + e0] >> Durshift) & Durlim;
              cxb = (ub4)(revr[e2 + zdayp2->pos] >> Durshift) & Durlim;
              if (cxb + durofs != cxa) break;
//              else if (cxb + durofs != cxa + 1 && cxa != cxb + durofs + 1) break;
            }
            dif = (e2 < len);
            if (dif) xrdurb++;
          } else {
            xrdurc++;
            dif = 1;
          }
          if (dif) {
            // infocc(dbg,Noiter," dif hop %u day %u dur",h,day2);
            continue;
          }
          rrefdaycnt++;
          zdayp->rday = day2; // todo zrefday
          break;
        } // each day2
        if (dif == 0) {
          break;
        }
        if (cmpevcnt > cmpevlim) break;
      } // each base hop in rid

      if (dif) {
        infocc(daypos <= 68,V0," pos %u dif day %u evs %u",daypos,day2,len);
        zevcnt += len;
        zhevcnt += len;
        zdayp->hop = zchop;
        zdayp->len = len;
        zdayp->pos = e0;
        zdayp->tday0 = tday0;
        zdayp->timchk = timchk;
        if (chp->daycnt == 0) {
          chp->daylolen = chp->dayhilen = len;
        } else {
          chp->daylolen = min(chp->daylolen,len);
          chp->dayhilen = max(chp->dayhilen,len);
        }
        chp->daycnt++;
        daypos++;
        infocc(daypos <= 68,V0,"day %u day2 %u pos %u",day,day2,daypos);
        if (prvmapz || day == 0) mapcnt2++;
        prvmapz = 0;
      } else {
//        infocc(daypos <= 68,Noiter," ref day %u evs %u pos %u",day2,len,daypos);
        zevcnt += 1;
        refs++;
        if (prvmapz) {
          if (tday0 != zdayp2->tday0 + daymin) mapcnt2++;
        } else mapcnt2++;
        prvmapz = 1;
      }
      error_ge(day,rngdy);
      day++;
      e0 = e;
      tday0 += daymin;
    } // each event

    dayskip += skip;
    daycnt += day;
    dayrefs += refs;
    totmapcnt2 += mapcnt2;
    error_gt(refs,day,0);

    info(V0,"%u day maps",mapcnt2);

    infocc(zchop < hopcnt,Iter|V0,"%u of %u days unique %u skipped, \ah%lu events len \ah%u,%u,%u tim \ah%u,\ah%u lim \ah%u",
      day - refs,day,skip,zevcnt,xrlen,xrlen1,xrlen2,xrtim1,xrtim2,xrlim);

    info(Notty|Iter,"%u of %u days unique, %u skips %u of %u events",day - refs,day,skip,zhevcnt,cevcnt);
    // if (dbg) break;
   } // each zndx

   msgprefix(0,"p2 rid %u",rid);

   rdaycnt += daycnt;
   rdayrefs += dayrefs;
   xlen += xrlen;
   xlen1 += xrlen1;
   xlen2 += xrlen2;
   xtim1 += xrtim1;
   xtim2 += xrtim2;
   xlim += xrlim;
   xdureq += xrdureq;
   xdura += xrdura;
   xdurb += xrdurb;
   xdurc += xrdurc;
   refdaycnt += rrefdaycnt;

   info(V0,"%u of %u days unique %u skipped, \ah%lu events len \ah%u tim \ah%u,\ah%u lim \ah%u",
      daycnt - dayrefs,daycnt,dayskip,zevcnt,xrlen,xrtim1,xrtim2,xrlim);

   info(Iter|V0,"\ah%u event\as",revcnt);
   p2evcnt += revcnt;
   error_gt(p2evcnt,p1evcnt,rid);

   infocc(do_compress && zevcnt != cumevcnt,Iter|V0,"compressed to \ah%lu from \ah%lu cevents in \ah%luB",zevcnt,cumevcnt,zevcnt * 8);
   info(Iter|V0,"\ah%u of \ah%u days identical",dayrefs,daycnt);

   totevmem2 = zevcnt * 8 + totmapcnt2 * 8;

   info(Iter|V0,"\ah%lu events \ah%lu event memory",zevcnt,totevmem2);
   info(Iter|V0,"xlen \ah%lu \ah%lu \ah%lu xtim \ah%lu,\ah%lu xdur \ah%lu \ah%lu \ah%lu",xlen,xlen1,xlen2,xtim1,xtim2,xdureq,xdura,xdurb);

   nocmpev = nocmpev1 + nocmpev2;
   info(CC0|V0,"\ah%u = \ah%u + \ah%u base events not in compound",nocmpev,nocmpev1,nocmpev2);

   aclear(acc1hist);
   aclear(acc2hist);
   aclear(acc3hist);

    // generate events, prepare pass
   for (hopndx = 0; hopndx < zcnt; hopndx++) {
     h = zlst[hopndx];
     error_ge(h,newhopcnt);
     infocc(h == hopdbg,Emp,"hop %u %u-%u",h,lohop,rhopcnt);
     // info(0,"hop %u %u-%u",h,lohop,rhopcnt);
     if (h < hopcnt) {
       error_lt(h,lohop);
       error_ge(h,lohop + rhopcnt);
     }
     chp = chops + h;
     thp = thops + h;
     chp1 = chops + chp->hop1;
     chp2 = chops + chp->hop2;
     error_z(thp->init1,h);
     error_nz(thp->init2,h);
     thp->init2 = 1;

     evcnt = chp->evcnt;
     warncc(evcnt == 0,Iter,"hop %u no evs from %u,%u",h,chp1->evcnt,chp2->evcnt);
     cev = cevents + cevofs;
     rev = ridevents + chp->evofs;
     // infocc(h == 35214,Emp,"rid %u %chop %u ofs %lu",chp->rid,hoptype(net,h),h,chp->evofs);

     acc1ei = thp->acc1ei;
     acc2ei = thp->acc2ei;
     acc3ei = thp->acc3ei;

     if (acc1ei == 0) hopmsgfln(FLN,Warn,0,h,"short acc at 0");

     acc1rt = rev[acc1ei] & Timlim;
     acc2rt = rev[acc2ei] & Timlim;
     acc3rt = rev[acc3ei] & Timlim;

     if (acc1rt == 0) hopmsg(Warn,0,h,"short acc t=0 at %u",acc1ei);
     if (acc2rt == 0) hopmsg(Warn,0,h,"med acc t=0 at %u",acc2ei);
     if (acc3rt == 0) hopmsg(Warn,0,h,"long acc t=0 at %u",acc3ei);

     for (rei = 0; rei < evcnt; rei++) {
       rx = rev[rei];
       rt = rx & Timlim;
       chk = (rx >> Accshift) & 0xff;
       // infocc(h == 35214,Emp,"rid %u hop %u chk %u ei %u ofs %lu",chp->rid,h,chk,rei,chp->evofs);
       if (chk != (h & 0xff)) return error(Emp,"%chop %u %x chk %x ei %u/%u",chp->ctype,h,h,chk,rei,evcnt);

       // create short accel
       while (acc1rt < rt + Acc1iv && acc1ei + 1 < evcnt) {
         acc1rt = rev[++acc1ei] & Timlim;
       }
       acc = (acc1ei - rei) & Acc1lim;
       // infocc(h == 0,0,"hop %u acc %u %u/%u \ad%u \ad%u",h,acc,hrei,rei,rt + gt0,hrt + gt0);
       // if (acc == 0) hopmsg(Fatal,0,h,"ev %u/%u hr1 %u",rei,evcnt,hrei);
       acc1hist[acc]++;

       // create medium accel
       while (acc2rt < rt + Acc2iv && acc2ei + 1 < evcnt) {
         acc2rt = rev[++acc2ei] & Timlim;
       }
       acc = (acc2ei - rei) & Acc2lim;
       acc2hist[acc]++;

       // create long accel
       while (acc3rt < rt + Acc3iv && acc3ei + 1 < evcnt) {
         acc3rt = rev[++acc3ei] & Timlim;
       }
       acc = (acc3ei - rei) & Acc3lim;
       acc3hist[acc]++;
     }

   } // each zndx

   // generate accel tables
   iac1len = mkacc(acc1hist,rp->acc1tab,acc1itab,Acc1len,&acc1limcnt,"short");
   rp->acc1len = iac1len;
   iac2len = mkacc(acc2hist,rp->acc2tab,acc2itab,Acc2len,&acc2limcnt,"med");
   rp->acc2len = iac2len;
   iac3len = mkacc(acc3hist,rp->acc3tab,acc3itab,Acc3len,&acc3limcnt,"long");
   rp->acc3len = iac3len;

   // generate events, generate pass
   for (hopndx = 0; hopndx < zcnt; hopndx++) {
     h = zlst[hopndx];
     chp = chops + h;
     thp = thops + h;

     evcnt = chp->evcnt;
     if (evcnt == 0) continue;

     chp1 = chops + chp->hop1;
     chp2 = chops + chp->hop2;

     cev = cevents + cevofs;
     rev = ridevents + chp->evofs;

     acc1ei = thp->acc1ei;
     acc2ei = thp->acc2ei;
     acc3ei = thp->acc3ei;

     acc1rt = rev[acc1ei] & Timlim;
     acc2rt = rev[acc2ei] & Timlim;
     acc3rt = rev[acc3ei] & Timlim;

     for (rei = 0; rei < evcnt; rei++) {
       rx = rev[rei];
       rt = rx & Timlim;
       dur = (rx >> Durshift) & Durlim;
       dtid = (rx >> Dtidshift) & Dtidlim;

       // create short accel
       while (acc1rt < rt + Acc1iv && acc1ei < evcnt) {
         acc1rt = rev[++acc1ei] & Timlim;
       }
       acc = (acc1ei - rei) & Acclim;
       iacc1 = acc1itab[acc];
       error_ge(iacc1,Acc1len);

       // create medium accel
       while (acc2rt < rt + Acc2iv && acc2ei < evcnt) {
         acc2rt = rev[++acc2ei] & Timlim;
       }
       acc = (acc2ei - rei) & Acclim;
       iacc2 = acc2itab[acc];
       error_ge(iacc2,Acc2len);

       // create long accel
       while (acc3rt < rt + Acc3iv && acc3ei < evcnt) {
         acc3rt = rev[++acc3ei] & Timlim;
       }
       acc = (acc3ei - rei) & Acclim;
       iacc3 = acc3itab[acc];
       error_ge(iacc3,Acc3len);

       rx  = ((ub8)iacc3 << Acc3shift) | ((ub8)iacc2 << Acc2shift) | ((ub8)iacc1 << Acc1shift);
       rx |= ((ub8)dtid << Dtidshift) | ((ub8)dur << Durshift) | rt;

       cev[rei] = rx;
     }

     chp->evofs = cevofs;
     cevofs += evcnt;
   } // each zndx

   msgprefix(0,NULL);

   // if (rid == 2) break;

  } // each rid
  chopcnt = chop;

  net->chopcnt = chopcnt;

  info(CC0|Emp,"%u of %u chop\as with no events",sumnocevcnt,chopcnt - hopcnt);
  if (sumnocevcnt * 2 > chopcnt - hopcnt) return error(0,"%u of %u chops with no events",sumnocevcnt,chopcnt - hopcnt);

  sumnocevcnt = 0;
  for (h = 0; h < chopcnt; h++) {
    chp = chops + h;
    thp = thops + h;
    error_z(thp->init1,h);
    error_z(thp->init2,h);
    if (chp->evcnt == 0) sumnocevcnt++;
  }
  info(CC0,"%u of %u chop\as with no events",sumnocevcnt,chopcnt - hopcnt);
  if (sumnocevcnt * 2 > chopcnt - hopcnt) return error(0,"%u of %u chops with no events",sumnocevcnt,chopcnt - hopcnt);

  info(0,"\ah%lu to \ah%lu events",p2evcnt,zevcnt);
  cumevcnt = p2evcnt;
  info(CC0,"\ah%lu variable sub event\as",varsdaofs);

  info(CC0,"\ah%u rids reaching accel 1 limit",acc1limcnt);
  info(CC0,"\ah%u rids reaching accel 2 limit",acc2limcnt);
  info(CC0,"\ah%u rids reaching accel 3 limit",acc3limcnt);

  infocc(docompound,0,"\ah%u compound hops, \ah%u with constant duration, \ah%u within 10 min",chop - hopcnt,eqdurs,aeqdurs);
  infocc(docompound,0,"avg chain len %u",(ub4)(cumchainlen / chaincnt));

  totevmem1 = cumevcnt * 8;

  info(0,"compression %sabled",do_compress ? "en" : "dis");
  info(0,"\ah%u day maps",totmapcnt2);
  info(Emp,"\ah%lu to \ah%lu+\ah%u = \ah%lu event memory \ap%lu%lu",
    totevmem1,zevcnt * 8,totmapcnt2 * 8,totevmem2,totevmem2,totevmem1);

  msgopt("pass2"); info(0,"xlen \ah%lu refs \ah%lu xtim \ah%lu,\ah%lu xdur \ah%lu \ah%lu \ah%lu \ah%lu",
       xlen,refdaycnt,xtim1,xtim2,xdureq,xdura,xdurb,xdurc);

  info(V0,"xlen \ah%lu,\ah%lu,\ah%lu xlim \ah%lu",xlen,xlen1,xlen2,xlim);

  if (varsdalen - varsdaofs > 1024 * 1024 * 8) trimblock(sdamem,varsdaofs,ub2);

  // free base hops
  afree(net->hops,"hops");
  hops = hp = net->hops = NULL;

  afree0(thops);

  // free base events
  trimblock(net->eventmem,0,ub8);

  // free rid events
  afree0(ridevents);

  if (docompound) {
    afree0(hopdtidlst);
    afree0(hopstlst);
    afree0(hop12lst);
    afree0(hophlst);
  }

  // count combis
  ub4 Chopcnt = 0, alconcnt = 0, onelinecnt = 0;
  ub4 car1,car2;
  ub1 *shares = net->shares;

  ub4 airhop1,airhop2,airhopcnt = 0;
  ub4 *airhops;

  if (docombine) {
    airhops = talloc(hopcnt,ub4,0xff,"airhops",0);
    for (hop = 0; hop < hopcnt; hop++) {
      chp = chops + hop;
      if (chp->kind != Airint && chp->kind != Airdom) continue;
      airhops[airhopcnt++] = hop;
    }

    for (airhop1 = 0; airhop1 < airhopcnt; airhop1++) {
      if (progress(&eta,"compound combis air hop %u of %u \ah%u",airhop1,airhopcnt,Chopcnt)) return 1;
      hop1 = airhops[airhop1];
      error_ge(hop1,hopcnt);
      chp1 = chops + hop1;
      car1 = chp1->carrier;
      if (car1 == hi32) continue;
      for (airhop2 = 0; airhop2 < airhopcnt; airhop2++) {
        if (airhop2 == airhop1) continue;
        hop2 = airhops[airhop2];
        error_ge_cc(hop2,hopcnt,"ahop %u of %u",airhop2,airhopcnt);
        chp2 = chops + hop2;
        if (chp1->arr != chp2->dep) continue;
        alconcnt++;
        car2 = chp2->carrier;
        if (car2 == hi32) continue;
        if (car1 == car2) onelinecnt++;
        else if (shares[car1 * Carriercnt + car2]) Chopcnt++;
      }
    }
    info(CC0,"\ah%u from \ah%u combined hops, \ah%u same carrier",Chopcnt,alconcnt,onelinecnt);
    afree0(airhops);
  }

  // check and update onerid
  for (hop = 0; hop < chopcnt; hop++) {
    dep = portsbyhop[hop * 2];
    arr = portsbyhop[hop * 2 + 1];
    if (dep == arr) continue;
    dist = hopdist[hop];
    pdep = ports + dep;
    parr = ports + arr;
    chp = chops + hop;
    if (hop < hopcnt) {
      chp = chops + hop;
      infocc(dist == 0,0,"hop %u %u-%u \ag%u %s to %s",hop,dep,arr,dist,pdep->name,parr->name);
      if (chp->tripstart) pdep->oneroute = 0;
      if (chp->tripend) parr->oneroute = 0;
    } else {
      hop1 = chp->hop1;
      hop2 = chp->hop2;
      error_ge(hop1,hopcnt);
      error_ge(hop2,hopcnt);
      infocc(dist == 0,0,"chop %u = %u-%u %u-%u \ag%u %s to %s",hop,hop1,hop2,dep,arr,dist,pdep->iname,parr->name);
    }
  }

  // allocate fare entries here, as they are for both plain and compound hops on reserved routes
  if (cumfhops == 0) return info0(0,"no fare entries");

  info(0,"\ah%lu + \ah%lu fare entries for %u hops",cumfevcnt,cumcfevcnt,cumfhops);

  if (globs.noreserve) return info0(0,"skip on disabled fares");

  cumfevcnt += cumcfevcnt;
  net->fareposcnt = cumfevcnt;

  ub4 *fhopofs = net->fhopofs = alloc(chopcnt,ub4,0xff,"fare fhopofs",cumfhops);

  ub4 *ridhops,*ridhopbase = net->ridhopbase;

  ub4 ofs = 0;
  ub4 h1ndx,h2ndx;
  info(0,"hopcnt %u chopcnt %u",hopcnt,chopcnt);
  for (hop = 0; hop < hopcnt; hop++) {
    chp = chops + hop;
    if (chp->reserve) {
      fhopofs[hop] = ofs;
      ofs += chp->evcnt;
    }
  }
  for (chop = hopcnt; chop < chopcnt; chop++) {
    chp = chops + chop;
    hop1 = chp->hop1;
    hop2 = chp->hop2;
    chp = chops + hop1;
    if (chp->reserve && fhopofs) {
      fhopofs[chop] = ofs;
      ofs += chp->evcnt;
    }
    rid = chp->rid;
    rp = routes + rid;
    rhopcnt = rp->hopcnt;
    hopndx = 0; h1ndx = h2ndx = hi32;
    ridhops = ridhopbase + rp->hop2pos;
    while (hopndx < min(rhopcnt,Chainlen) && (h1ndx == hi32 || h2ndx == hi32)) {
      h = rp->hops[hopndx];
      if (h == hop1) h1ndx = hopndx;
      else if (h == hop2) h2ndx = hopndx;
      hopndx++;
    }
    if (h1ndx == hi32 || h2ndx == hi32) {
      vrb0(0,"rid %u hop %u-%u not found at %u-%u chop %u",rid,hop1,hop2,h1ndx,h2ndx,chop);
      continue;
    }
    error_ge(h1ndx,rhopcnt);
    error_ge(h2ndx,rhopcnt);
    ridhops[h1ndx * rhopcnt + h2ndx] = chop;
  }
  error_ne(ofs,cumfevcnt);
  ub2 fare,*farepos,*fareposbase = net->fareposbase = mkblock(&net->faremem,cumfevcnt * Faregrp,ub2,Init0,"fare entries for %u reserved hops",cumfhops);

  if (do_rndfares == 0) return 0;

  for (chop = 0; chop < chopcnt; chop++) {
    chp = chops + chop;
    if (chp->reserve == 0) continue;
    ofs = fhopofs[chop];
    evcnt = chp->evcnt;
    farepos = fareposbase + Faregrp * ofs;
    for (e = 0; e < evcnt; e++) {
      fare = (ub2)rnd(chp->dist / 100);
      farepos[e * Faregrp] = fare;
    }
  }

  return 0;
}

int compound(gnet *net)
{
  ub4 portcnt = net->portcnt;
  ub4 hopcnt = net->hopcnt;
  ub4 ridcnt = net->ridcnt;

  ub4 hichainlen = net->hichainlen;

  int docompound = dorun(FLN,Runcompound,0);

  int do_compress = (globs.noevcompress == 0);

  if (hopcnt == 0) return error0(0,"no compound on no hops");
  if (portcnt < 2) return error(0,"no compound on %u port\as",portcnt);
  if (ridcnt == 0) return error(0,"no compound on no rids for %u hop\as",hopcnt);

  if (docompound) {
    info(0,"compounding %u ports %u hops max chain %u",portcnt,hopcnt,hichainlen);
  } else info0(0,"compound not enabled");
  return do_compound(net,docompound,do_compress);
}
