// net2.c - precompute 2-stop connections

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2016 Joris van der Geer.
 */

/* Initialize the network once at startup :

  for each dep
    for each via1 = direct arr from dep
      for each via2 = direct arr from via1
        for each arr = direct arr from via2

   create a pre-computed 2-stop connectivity network used in search

   - Build connectivity matrix between any 2 full ports
     derived matrix for each of n intermediate hops

     each matrix contains a list of possible trips from port A to port B
     the list is limited to a top-n on average trip duration, and trimmed on heuristics such as distance, cost, timing

     base matrix for direct (non-stop) hops is prepared in net.c
 */

#include <string.h>
#include <pthread.h>
#include <sched.h>

#include "base.h"
#include "cfg.h"
#include "mem.h"
#include "os.h"
#include "math.h"

static ub4 msgfile;
#include "msg.h"

#include "iadr.h"
#include "util.h"
#include "time.h"
#include "net.h"
#include "net2.h"
#include "netev.h"

#undef hdrstop

static int vrbena;

void ininet2(void)
{
  msgfile = setmsgfile(__FILE__);
  iniassert();
  vrbena = (getmsglvl() >= Vrb);
}

// max number of alternatives per dep,arr pair to consider
#define Durcnt 256

static const ub4 no_airsep = 1; // pending change to un/reserved

static const ub8 sumreach = 1000 * 100;  // treat as hub if sum of direct reachable dest above

// heuristic limit for over-route net2 versus direct
static ub4 geodistlim(ub4 dir)
{
  ub4 lim = 0;

  if (dir <= 100) return dir * 10;
  if (dir > 100) { lim += 100 * 10; dir -= 100; }
  if (dir > 1000) { lim += 1000 * 5; dir -= 1000; }
  if (dir > 10000) { lim += 10000 * 5; dir -= 10000; }
  if (dir > 100000) { lim += 100000 * 4; dir -= 100000; }
  if (dir > 500000) { lim += 500000 * 3; dir -= 500000; }
  lim += dir * 2;
  return lim;
}

// geographical direct line distance from grid or direct
static ub4 xgeodist(struct port *pdep,struct port *parr,ub4 seqdep,ub8 gseqcnt,ub2 *seqdist)
{
  ub4 dir;

  if (seqdist && (pdep->gridlat + 1 < parr->gridlat || pdep->gridlon + 1 < parr->gridlon
    || parr->gridlat + 1 < pdep->gridlat || parr->gridlon + 1 < pdep->gridlon) ) {
    dir = (ub4)seqdist[(ub8)seqdep * gseqcnt + parr->gridseq] << Gridshift;
  } else dir = fgeodist(pdep,parr,1);
  return dir;
}

static ub4 getvarlim(struct port *pdep,struct port *parr,int *hub)
{
  ub4 nda = max(pdep->nda,parr->nda);

  *hub = 0;
  if (nda < globs.net2con[0]) {
    if (pdep->sumreach > sumreach || parr->sumreach >sumreach) return globs.net2limit[0];
    else return 0;
  }
  else if (nda < globs.net2con[1]) return globs.net2limit[0];
  else if (nda < globs.net2con[2]) return globs.net2limit[1];
  else {
    *hub = 1;
    return globs.net2limit[2];
  }
}

/*
  mid1:12
  mid2:12
  v1:8
  v2:8
  v3:8
  dur:16
*/
#define Lst2midbit 12
#define Lst2vbit 8
#define Lst2dbit 16

#define Lst2midcnt (1 << Lst2midbit)
#define Lst2mmask (Lst2midcnt - 1)
#define Lst2m2shift Lst2midbit
#define Lst2vcnt (1 << Lst2vbit)
#define Lst2vmask (Lst2vcnt - 1)
#define Lst2v1shift (Lst2midbit + Lst2midbit)
#define Lst2v2shift (Lst2v1shift + Lst2vbit)
#define Lst2v3shift (Lst2v2shift + Lst2vbit)
#define Lst2durshift (Lst2v3shift + Lst2vbit)
#if Lst2durshift > (64 - 16)
#error "Lst2durshift too large"
#endif

#define Lst2durcnt (1 << Lst2dbit)

// max number of each via stop to consider for net2
#define Viacnt2 Lst2midcnt

struct net2_p2_args {
// in
  ub4 tid,tidcnt;
  struct network *net;
  ub4 depfrom,depto;
  ub4 lowcon;
  int nice;

  ub4 varlimit,var12limit,cntonly;
  ub4 distabove_da,distabove_da1;
  int net1;

  ub4 *depmid1s;
  ub4 *depmid1durs;
  ub4 *depmid1ds;
  ub4 *depmid1cnts;
  ub4 *dmid1cnts;
  ub8 dmid1sort[Viacnt2];

  ub4 *arrmid2s;
  ub4 *arrmid2ds;
  ub4 *arrmid2cnts;
  ub4 *dmid2cnts;

// out
  int rv;
  ub8 lstlen;
};

// 2-stop net pass 1, runs a departure port set per thread
// count in precnts, durlegs01 and -2d
static int net2_pas1(struct net2_p2_args *argp)
{
  ub4 tid = argp->tid;
  ub4 tidcnt = argp->tidcnt;
  ub4 msgtid;

  ub4 *depmid1s = argp->depmid1s;
  ub4 *dmid1ds,*depmid1ds = argp->depmid1ds;
  ub4 *depmid1cnts = argp->depmid1cnts;
  ub4 *dmid1cnts  = argp->dmid1cnts;

  ub4 *arrmid2s = argp->arrmid2s;
  ub4 *dmid2ds,*arrmid2ds = argp->arrmid2ds;
  ub4 *arrmid2cnts = argp->arrmid2cnts;
  ub4 *dmid2cnts  = argp->dmid2cnts;

  ub4 *dmid1s,*dmid2s;
  ub4 *dmid1acnt,*dmid2acnt;
  ub4 dmid1cnt,dmid2cnt;

  ub4 varlimlh;
  ub4 varlimit = argp->varlimit;
  ub4 var12limit = argp->var12limit;
  ub4 cntonly = argp->cntonly;
  ub4 lowcon = argp->lowcon;
  ub4 distabove_da = argp->distabove_da;
  ub4 distabove_da1 = argp->distabove_da1;

  int net1 = argp->net1;

  struct network *net = argp->net;

  ub4 portcnt = net->portcnt;
  struct port *pdep,*parr,*pmid1,*pmid2,*ports = net->ports;
  iadrbase *cnts0,*cnts1,*precnts;
  ub4 dep,mid1,mid2,arr;
  ub4 dmid1,dmid2;
  ub4 cnt,n1,n2,n3,n123;
  ub4 dirdist,gdistlim,dirdistdm,dirdistm1a,dirdistma,dirdistm12;
  ub4 cntlim,depair,arrair,deparrair;
  int ishub;

  ub4 seqdep,seqarr,seqm1;
  ub4 gseqcnt = net->seqdlen;
  ub2 *seqdist = net->seqdist;
  ub1 lotx,*seqlotx = net->seqlotx;

  ub8 stat_var12lim = 0,stat_distlim1 = 0,stat_distlim2 = 0,stat_distlim3 = 0,stat_distlim4 = 0;
  ub8 stat_net1lim = 0,stat_abvdist = 0,stat_locon = 0,stat_lotx = 0;

  struct eta eta;

  ub8 lstlen = 0,pairs = 0;
  ub4 depfrom = argp->depfrom;
  ub4 depto = argp->depto;

  ports = net->ports;

  precnts = &net->conipos;

  cnts0 = net->concnt;
  cnts1 = net->concnt + 1;

  iadrbase *lstitems = &net->lst2items;

  if (tidcnt > 1) {
    msgtid = (tid << Tidshift) | Tidbit;
    info(msgtid,"start in thread %u",tid);
  } else msgtid = 0;

  // for each departure port
  for (dep = depfrom; dep < depto; dep++) {

    if (tprogress(tid,tidcnt,&eta,"p1 port %u/%u \ah%lu conns",dep - depfrom,depto - depfrom,lstlen)) return 1;

    pdep = ports + dep;
    if (pdep->valid == 0) continue;
    depair = (pdep->modes & Airbit);

    if (depair == 0 && pdep->nda < lowcon && pdep->sumreach < sumreach) { stat_locon++; continue; }

    dmid1s = depmid1s + dep * Viacnt2;
    dmid1ds = depmid1ds + dep * Viacnt2;
    dmid1acnt = depmid1cnts + dep * Viacnt2;
    dmid1cnt = dmid1cnts[dep];

    if (dmid1cnt == 0) continue;

    if (pairs + portcnt >= hi32) {
      warn(0,"limiting pairs to \ah%lu at dep %u",pairs,dep);
      break;
    }

    seqdep = pdep->gridseq;

    // for each arrival port
    for (arr = 0; arr < portcnt; arr++) {
      if (arr == dep) continue;

      parr = ports + arr;
      if (parr->valid == 0) continue;

      seqarr = parr->gridseq;
      if (net->havelotx && seqdep != seqarr) {
        lotx = seqlotx[(ub8)seqdep * gseqcnt + seqarr];
        if (lotx > 2) { stat_lotx++; continue; }
      }

      arrair = (parr->modes & Airbit);
      deparrair = depair | arrair;

      if (deparrair == 0 && parr->nda < lowcon && parr->sumreach < sumreach) { stat_locon++; continue; }

      varlimlh = getvarlim(pdep,parr,&ishub);
      error_gt(varlimlh,varlimit,0);
      if (varlimlh == 0) continue;

      if (cntonly < 256) {
        n1 = rdiadr2(cnts0,dep,arr);
        if (n1 > cntonly) continue;
        n1 += rdiadr2(cnts1,dep,arr);
        if (n1 > cntonly) continue;
      }

      cnt = 0;

      dmid2s = arrmid2s + arr * Viacnt2;
      dmid2ds = arrmid2ds + arr * Viacnt2;
      dmid2acnt = arrmid2cnts + arr * Viacnt2;
      dmid2cnt = dmid2cnts[arr];

      if (dmid2cnt == 0) continue;

      seqarr = parr->gridseq;

      dirdist = xgeodist(pdep,parr,seqdep,gseqcnt,seqdist);

      if (dirdist < distabove_da) { stat_abvdist++; continue; }
      else if (dirdist < distabove_da1) {
        if ( !(pdep->modes & Walkbit) || !(parr->modes & Walkbit) ) continue;
      }
      gdistlim = geodistlim(dirdist);

      // for each via1
      for (dmid1 = 0; cnt < varlimlh && dmid1 < dmid1cnt; dmid1++) {

        mid1 = dmid1s[dmid1];
        if (mid1 == arr) continue;

        dirdistdm = dmid1ds[dmid1];
        if (dirdistdm > gdistlim) {
          stat_distlim1++;
          // info(Notty|Noiter|msgtid,"dir %u distdm %u above %u %s - %s",dirdist,dirdistdm,gdistlim,pdep->name,parr->name);
          continue;
        }

        mid1 = dmid1s[dmid1];
        if (mid1 == arr) continue;

        if (net1) {
          n1 = rdiadr2(cnts1,mid1,arr);
          if (n1 == 0) { stat_net1lim++; continue; }
        }

        pmid1 = ports + mid1;
        seqm1 = pmid1->gridseq;

        dirdistm1a = xgeodist(pmid1,parr,seqm1,gseqcnt,seqdist);

        if (dirdistdm + dirdistm1a > gdistlim) {
          stat_distlim2++;
          // info(Notty|Noiter|msgtid,"dir %u distdma %u above %u %s - %s",dirdist,dirdistdm + dirdistm1a,gdistlim,pdep->name,parr->name);
          continue;
        }

        // if (deparrair == 0 && ishub == 0 && midair == 0 && dirdistm1a < distabove_da) continue;
        if (dirdistm1a < distabove_da) continue;

        n1 = dmid1acnt[dmid1];
        error_z(n1,dmid1);

        // for each via2
        for (dmid2 = 0; cnt < varlimlh && dmid2 < dmid2cnt; dmid2++) {

          mid2 = dmid2s[dmid2];

          dirdistma = dmid2ds[dmid2];
          if (dirdistdm + dirdistma > gdistlim) {
            stat_distlim3++;
            // info(Notty|Noiter|msgtid,"dir %u distdm %u above %u %s - %s",dirdist,dirdistdm + dirdistma,gdistlim,pdep->name,parr->name);
            continue;
          }

          mid2 = dmid2s[dmid2];
          if (mid2 == mid1 || mid2 == dep) continue;

          n3 = dmid2acnt[dmid2];
          error_z(n3,dmid2);

          n2 = rdiadr2(cnts0,mid1,mid2);
          if (n2 == 0) continue;
          n2 = min(n2,Lst2vmask);

          pmid2 = ports + mid2;

          dirdistm12 = xgeodist(pmid1,pmid2,seqm1,gseqcnt,seqdist);

          if (dirdistdm + dirdistm12 + dirdistma > gdistlim) {
            stat_distlim4++;
            // info(Notty|Noiter|msgtid,"dir %u distdm %u above %u %s - %s",dirdist,dirdistdm + dirdistm12,gdistlim,pdep->name,parr->name);
            continue;
          }

          n123 = n1 * n2 * n3;

          if (n123 > var12limit) { n123 = var12limit; stat_var12lim++; }
          cnt += n123;
        } // each mid2
      } // each mid1

      cntlim = min(cnt,varlimlh);

      if (cntlim) {
        if (iadrinc(precnts,dep,arr,tid)) return info(Ret1,"dep %u arr %u",dep,arr);
        iadrincn(lstitems,dep,arr * varlimit,cntlim,tid);
        lstlen += cntlim;
        pairs++;
      }

    } // each arr

  } // each dep
  argp->lstlen = lstlen;

  info(msgtid,"limits dist abv \ah%lu dm \ah%lu da \ah%lu m2a \ah%lu dma \ah%lu ",
    stat_abvdist,stat_distlim1,stat_distlim2,stat_distlim3,stat_distlim4);
  info(msgtid,"  net1 \ah%lu var \ah%lu locon \ah%lu  lotx \ah%lu",stat_net1lim,stat_var12lim,stat_locon,stat_lotx);

  return info(msgtid,"tid %u 2-stop pass 1 \ah%lu tentative triplets",tid,lstlen);
} // 2-stop pass 1

static void *net2_pass1(void *vp)
{
  struct net2_p2_args *argp = (struct net2_p2_args *)vp;
  ub4 tid = argp->tid;
  globs.tids[tid] = 1;
  ub4 msgtid = (tid << Tidshift) | Tidbit;
  if (argp->nice) {
    ossetprio(argp->nice);
    info(msgtid,"nice value %d",argp->nice);
  }
  int rv = net2_pas1(argp);
  argp->rv = rv;
  globs.tids[tid] = 0;
  return vp;
}

// 2-stop net pass 2, runs a departure port set per thread
// result counts stored in cnts, triplets in durlegs01 and -2d
static int net2_pas2(struct net2_p2_args *argp)
{
  ub4 tid = argp->tid;
  ub4 tidcnt = argp->tidcnt;
  ub4 msgtid;

  ub4 *depmid1s = argp->depmid1s;
  ub4 *depmid1durs = argp->depmid1durs;
  ub4 *dmid1ds,*depmid1ds = argp->depmid1ds;
  ub4 *depmid1cnts = argp->depmid1cnts;
  ub4 *dmid1cnts  = argp->dmid1cnts;
  ub8 x8,*dmid1sort = argp->dmid1sort;
  ub4 *arrmid2s = argp->arrmid2s;
  ub4 *dmid2ds,*arrmid2ds = argp->arrmid2ds;
  ub4 *arrmid2cnts = argp->arrmid2cnts;
  ub4 *dmid2cnts  = argp->dmid2cnts;

  ub4 *dmid1s,*dmid2s,*dmid1durs;
  ub4 *dmid1acnt,*dmid2acnt;
  ub4 dmid1cnt,sdmid1cnt,dmid2cnt;

  ub4 varlimlh;
  ub4 varlimit = argp->varlimit;
  ub4 var12limit = argp->var12limit;
  ub4 distabove_da = argp->distabove_da;
  ub4 distabove_da1 = argp->distabove_da1;
  ub4 distabove_da10 = distabove_da * 10;

  ub4 cntonly = argp->cntonly;
  ub4 lowcon = argp->lowcon;

  int net1 = argp->net1;

  struct network *net = argp->net;

  ub4 portcnt = net->portcnt;
  ub4 thopcnt = net->thopcnt;
  ub4 whopcnt = net->whopcnt;
  struct port *pdep,*parr,*pmid1,*pmid2,*ports = net->ports;
  struct chop *hp2,*hp3,*hops = net->chops;
  block *lstblk0;
  ub4 *portsbyhop;
  iadrbase *cnts0,*cnts1,*precnts,*cnts;
  iadrbase *conofs0;
  ub8 ofs1,ofs2,ofs3;
  ub4 *conlst1,*lst1,*lst2,*lst3;
  ub4 *hopdist = net->hopdist;
  ub1 leg123mode,*hopmode = net->hopmodes;
  ub4 air,aircnt;
  ub4 lodur1,lodur2,lodur3;
  ub4 rid1;
  ub4 dep,mid1,mid2,arr;
  ub4 dmid1,sdmid1,dmid2;
  ub4 n1,n2,n3,n123,altcnt,v1,v2,v3,leg1,leg2,leg3;
  ub8 lstlen;
  ub4 dist1,dist2,dist3;
  ub4 dirdist,gdistlim,dirdistdm,dirdistm1a,dirdistma,dirdistm12;
  ub4 wxw,depair,arrair,deparrair;
  ub4 sumwalkdist1,sumwalkdist2,sumwalkdist3;
  ub4 cntlimdur,gen,outcnt;
  int ishub;
  ub8 timlim;

  ub4 n,midur,durndx,durcnt,durlim,durlim1,durcntgnd,durlimgnd,durdist;
  ub4 dtlo,dthi,typdt,dtcnt;
  ub4 midurs[Durcnt],midursgnd[Durcnt];
  ub4 sortdurs[Durcnt];
  ub4 tmpmodes[Durcnt];
  ub8 tmpitem,tmpitems[Durcnt],tmpitemsgnd[Durcnt];

  ub4 sumwalklimit = net->sumwalklimit;
  ub4 stat_partlimdur = 0;
  ub8 stat_noestdur = 0,stat_estdur = 0;
  ub8 stat_var12lim = 0,stat_distlim1 = 0,stat_distlim2 = 0,stat_distlim3 = 0,stat_distlim4 = 0;
  ub8 stat_net1lim = 0,stat_timlim = 0,stat_timlim2 = 0,stat_lotx = 0,stat_varlim = 0;
  ub8 stat_da1 = 0,stat_da2 = 0,stat_da3 = 0;
  ub4 hialt = 0,altdep = 0,altarr = 0;
  ub8 nogen = 0,sumoutcnt = 0;

  struct eta eta;
  int cmd;

  lstlen = 0;
  ub4 depfrom = argp->depfrom;
  ub4 depto = argp->depto;

  ub4 da_timlim = globs.net2timlim;
  ub4 altlim,da_altlim = globs.net2altlim;

  ports = net->ports;

  portsbyhop = net->portsbyhop;

  precnts = &net->conipos;
  conofs0 = net->conofs;

  cnts0 = net->concnt;
  cnts1 = net->concnt + 1;
  cnts = net->concnt + 2;

  lstblk0 = net->conlst;
  conlst1 = blkdata(lstblk0,0,ub4);

  iadrbase *durlims1 = net->durlims + 1;

  iadrbase *lstitems = &net->lst2items;
  ub4 hindx,hidur;

  ub4 seqdep,seqarr,seqm1;
  ub4 gseqcnt = net->seqdlen;
  ub2 *seqdist = net->seqdist;
  ub1 lotx,*seqlotx = net->seqlotx;

  if (tidcnt > 1) {
    msgtid = (tid << Tidshift) | Tidbit;
    info(msgtid,"start in thread %u",tid);
  } else msgtid = 0;

  for (dep = depfrom; dep < depto; dep++) {

    pdep = ports + dep;

    cmd = tprogress(tid,tidcnt,&eta,"p2 port %4u/%u  \ah%lu con %17s",dep - depfrom,depto - depfrom,lstlen,pdep->prefix);

    switch(cmd) {
    case 0: break;
    case 1: return 2;
    case 2: info(0,"time limit from %u to %u",da_timlim,da_timlim / 10);
            da_timlim /= 10;
            break;
    default: break;
    }

    if (pdep->valid == 0) continue;

    depair = (pdep->modes & Airbit);

    if (depair == 0 && pdep->nda < lowcon && pdep->sumreach < sumreach) continue;

    dmid1s = depmid1s + dep * Viacnt2;
    dmid1durs = depmid1durs + dep * Viacnt2;
    dmid1ds = depmid1ds + dep * Viacnt2;
    dmid1acnt = depmid1cnts + dep * Viacnt2;
    dmid1cnt = dmid1cnts[dep];

    if (dmid1cnt == 0) continue;

    outcnt = 0;

    if (sumoutcnt + portcnt >= hi32) {
      warn(msgtid,"limiting pairs to \ah%lu at dep %u of %u",sumoutcnt,dep,portcnt);
      break;
    }

    seqdep = pdep->gridseq;

    // for each arrival port
    for (arr = 0; arr < portcnt; arr++) {
      if (arr == dep) continue;

      parr = ports + arr;
      if (parr->valid == 0) continue;

      seqarr = parr->gridseq;
      if (net->havelotx && seqdep != seqarr) {
        lotx = seqlotx[(ub8)seqdep * gseqcnt + seqarr];
        if (lotx > 2) { stat_lotx++; continue; }
      }

      arrair = (parr->modes & Airbit);
      deparrair = depair | arrair;

      if (deparrair == 0 && parr->nda < lowcon && parr->sumreach < sumreach) continue;

      dmid2s = arrmid2s + arr * Viacnt2;
      dmid2ds = arrmid2ds + arr * Viacnt2;
      dmid2acnt = arrmid2cnts + arr * Viacnt2;
      dmid2cnt = dmid2cnts[arr];

      if (dmid2cnt == 0) continue;

      if (cntonly < 256) {
        n1 = rdiadr2(cnts0,dep,arr);
        if (n1 > cntonly) continue;
        n1 += rdiadr2(cnts1,dep,arr);
        if (n1 > cntonly) continue;
      }

      varlimlh = getvarlim(pdep,parr,&ishub);
      if (varlimlh == 0) { stat_varlim++; continue; }
      error_gt(varlimlh,varlimit,arr);

      timlim = da_timlim;
      altlim = da_altlim;
      if (ishub || deparrair) {
        timlim *= 4;
        altlim *= 10;
      }

      cntlimdur = min(varlimlh,Durcnt-1);

      dirdist = xgeodist(pdep,parr,seqdep,gseqcnt,seqdist);

//      if (deparrair == 0 && ishub == 0) {
        if (dirdist < distabove_da) { stat_distlim1++; continue; }
        else if (dirdist < distabove_da1) {
          if ( (pdep->modes & Walkbit) && (parr->modes & Walkbit) ) wxw = 1;
          else { stat_distlim1++; continue; }
        } else wxw = 0;
//      } else wxw = 0;

      gdistlim = geodistlim(dirdist);

      gen = 0;

      // start with limits derived from previous nstop

      // prepare sort on time.

      if (dirdist < 10) { durlim = 60; timlim /= 500; }
      else if (dirdist < 1 * 100) { durlim = 2 * 60; timlim /= 500; }
      else if (dirdist < 10 * 100) { durlim = 12 * 60; timlim /= 200;}
      else if (dirdist < 100 * 100) { durlim = 1 * 1440; timlim /= 40; }
      else if (dirdist < 1000 * 100) { durlim = 4 * 1440; timlim /= 10; }
      else if (dirdist < 10000 * 100) durlim = 8 * 1440;
      else durlim = 14 * 1440;
      durlimgnd = durlim;

      timlim = max(timlim,1);
      setthtimer(tid,(ub4)timlim);

      if (net1) durlim1 = rdiadr2(durlims1,dep,arr);
      else durlim1 = 0;
      if (durlim1 == 0) durlim1 = hi16;
      if (durlim1 != hi16) durlim1 = (durlim1 * 3) / 2 + dirdist / 100 + 30;

      nsethi(midurs,Durcnt);
      nsethi(midursgnd,cntlimdur);

      // create time top-n list, derive threshold
      altcnt = 0;
      durcnt = 0;
      durcntgnd = 0;

      // sort and filter via1 on distance to arr
      sdmid1cnt = 0;
      for (dmid1 = 0; dmid1 < dmid1cnt; dmid1++) {
        mid1 = dmid1s[dmid1];
        if (mid1 == arr) continue;

        pmid1 = ports + mid1;

        seqm1 = pmid1->gridseq;
        dirdistm1a = xgeodist(pmid1,parr,seqm1,gseqcnt,seqdist);

        // if (deparrair == 0 && ishub == 0 && midair == 0 && dirdistm1a < distabove_da) continue;
        if (dirdistm1a < distabove_da) { stat_distlim2++; continue; }
        if (dirdistm1a > gdistlim) { stat_distlim3++; continue; }

        durdist = dirdistm1a + dmid1durs[dmid1] * 50;
        dmid1sort[sdmid1cnt++] = ((ub8)durdist << 32) | dmid1;
      }
      if (sdmid1cnt * dmid2cnt > 64 * 64) fsort8(dmid1sort,sdmid1cnt,1,FLN,"dmid1");

      // each via1
      for (sdmid1 = 0; sdmid1 < sdmid1cnt; sdmid1++) {
        x8 = dmid1sort[sdmid1];
        dirdistm1a = (ub4)(x8 >> 32);

        dmid1 = x8 & hi32;
        error_ge(dmid1,dmid1cnt);
        dirdistdm = dmid1ds[dmid1];
        if (dirdistdm > gdistlim) { stat_distlim4++; continue; }

        mid1 = dmid1s[dmid1];
        if (mid1 == arr) continue;

        if (net1) {
          n1 = rdiadr2(cnts1,mid1,arr);
          if (n1 == 0) { stat_net1lim++; continue; }
        }

        if (dirdist < distabove_da10 && altcnt > altlim) break;

        if (gen && isexpired(tid)) {
          stat_timlim++;
          if (dirdist >= distabove_da10) {
            stat_timlim2++;
            info(msgtid,"timeout %u ms at dist \ag%u dep %u arr %u %s",(ub4)timlim,dirdist,dep,arr,pdep->prefix);
            info(msgtid," %s - %s",pdep->name,parr->iname);
          }
          break;
        }

        pmid1 = ports + mid1;
        if (dirdistdm + dirdistm1a > gdistlim) continue;

        n1 = dmid1acnt[dmid1];
        ofs1 = rdiadr8(conofs0,dep,mid1);
        seqm1 = pmid1->gridseq;

        // each via2
        for (dmid2 = 0; dmid2 < dmid2cnt; dmid2++) {
          dirdistma = dmid2ds[dmid2];
          if (dirdistdm + dirdistma > gdistlim) continue;

          mid2 = dmid2s[dmid2];
          if (mid2 == mid1 || mid2 == dep) continue;

          n2 = rdiadr2(cnts0,mid1,mid2);
          if (n2 == 0) continue;
          n2 = min(n2,Lst2vmask);

          pmid2 = ports + mid2;
          dirdistm12 = xgeodist(pmid1,pmid2,seqm1,gseqcnt,seqdist);

          if (dirdistdm + dirdistm12 + dirdistma > gdistlim) continue;

          n3 = dmid2acnt[dmid2];

          n123 = 0;

          ofs2 = rdiadr8(conofs0,mid1,mid2);
          ofs3 = rdiadr8(conofs0,mid2,arr);

          error_eq(ofs1,hi32);
          error_eq(ofs2,hi32);
          error_eq(ofs3,hi32);

          lst1 = conlst1 + ofs1;
          lst2 = conlst1 + ofs2;
          lst3 = conlst1 + ofs3;

          bound(lstblk0,ofs1,ub4);
          bound(lstblk0,ofs2,ub4);
          bound(lstblk0,ofs3,ub4);

          stat_da1++;

          // each dep-via1-via2-arr alternative
          for (v1 = 0; v1 < n1 && n123 < var12limit; v1++) {
            leg1 = lst1[v1];
            if (leg1 == hi32) {
              error(msgtid,"invalid trip %u-%u-%u-%u",dep,mid1,mid2,arr);
              break;
            }
            error_ge(leg1,whopcnt);

            if (portsbyhop[leg1 * 2] != dep) {
              info(msgtid,"hop %u %u-%u vs %u-%u",leg1,portsbyhop[leg1 * 2],portsbyhop[leg1 * 2 + 1],dep,mid1);
              continue;
            }

            lodur1 = hops[leg1].lodur;

            dist1 = hopdist[leg1];
            if (dist1 > gdistlim) continue;

            air = (hopmode[leg1] & Airbit) | no_airsep;
            if (lodur1 > (air ? durlim : durlimgnd)) continue;

            if (leg1 >= thopcnt) sumwalkdist1 = dist1;
            else {
              if (wxw) continue; // only walk-any-walk below a given dist
              sumwalkdist1 = 0;
            }

            rid1 = hops[leg1].rid;

            stat_da2++;

            for (v2 = 0; v2 < n2 && n123 < var12limit; v2++) {
              leg2 = lst2[v2];

              hp2 = hops + leg2;
              if (rid1 == hp2->rid && hp2->tripstart == 0) continue;

              lodur2 = lodur1 + hops[leg2].lodur;

              dist2 = dist1 + hopdist[leg2];
              if (dist2 > gdistlim) continue;

              sumwalkdist2 = sumwalkdist1;

              if (leg2 >= thopcnt) {
                if (leg1 >= thopcnt) continue;
                sumwalkdist2 += hopdist[leg2];
              }

              if (sumwalkdist2 > sumwalklimit) continue;

              stat_da3++;

              for (v3 = 0; v3 < n3 && n123 < var12limit; v3++) {
                n123++;
                leg3 = lst3[v3];

                hp3 = hops + leg3;
                if (hp2->rid == hp3->rid && (hp2->tripend == 0 || hp3->tripstart == 0)) continue;

                leg123mode = hopmode[leg1] | hopmode[leg2] | hopmode[leg3];
                air = (leg123mode & Airbit) | no_airsep;

                lodur3 = lodur2 + hops[leg3].lodur;

                if (lodur3 > (air ? durlim : durlimgnd)) continue;

                dist3 = dist2 + hopdist[leg3];
                if (dist3 > gdistlim) continue;

                if (leg3 >= thopcnt) {
                  if (leg2 >= thopcnt) continue;
                  sumwalkdist3 = sumwalkdist2 + hopdist[leg3];
                  if (sumwalkdist3 > sumwalklimit) continue;
                } else if (wxw) continue; // only walk-any-walk below a given dist

                // maintain top-n list with corresponding triplet
                // insertion sort
                dtcnt = estdur_3(net,leg1,leg2,leg3,&dtlo,&dthi,&typdt);
                midur = typdt;
                if (dtcnt == 0) {
                  stat_noestdur++;
                  // warn(msgtid,"no estdur for %u-%u-%u",leg1,leg2,leg3);
                  continue;
                } else if (midur > Lst2durcnt) {
                  warn(0,"durlim %u exceeds %u",midur,Lst2durcnt);
                  continue;
                }
                altcnt++;
                stat_estdur++;
                if (no_airsep && midur > durlim) continue;
                if (midur > (air ? durlim : durlimgnd)) continue;

                tmpitem =  (ub8)dmid1 | ((ub8)dmid2 << Lst2m2shift);
                tmpitem |= ((ub8)v1 << Lst2v1shift) | ((ub8)v2 << Lst2v2shift) | ((ub8)v3 << Lst2v3shift);
                tmpitem |= ((ub8)midur << Lst2durshift);

                // store in both mixed mode and ground-only. select part of each if needed lateron
                if (durcnt == 0) {
                  tmpitems[0] = tmpitem;
                  tmpmodes[0] = leg123mode;
                  midurs[0] = midur;
                  warncc(midur != hi32 && midur > 65534,Exit|msgtid,"durlim %u at 0 of %u exceeds 64k",midur,cntlimdur);
                  durcnt = 1;
                  gen++;
                } else if (cntlimdur < varlimit && midur > durlim1 && durcnt >= cntlimdur / 2) { // second half must be better than net1
                  durlim = min(durlim,durlim1);
                  continue;
                } else if (durcnt < cntlimdur) {
                  warncc(midur != hi32 && midur > 65534,Exit|msgtid,"durlim %u at %u of %u exceeds 64k",midur,durcnt,cntlimdur);
                  tmpitems[durcnt] = tmpitem;
                  tmpmodes[durcnt] = leg123mode;
                  midurs[durcnt++] = midur;
                  gen++;
                } else {
                  hidur = hindx = 0;
                  for (durndx = 0; durndx < cntlimdur; durndx++) {
                    if (midurs[durndx] > hidur) {
                      hidur = midurs[durndx];
                      hindx = durndx;
                    }
                    warncc(midurs[durndx] != hi32 && midurs[durndx] > 65534,Exit|msgtid,"durlim %u at %u of %u exceeds 64k",midurs[durndx],durndx,cntlimdur);
                  }
                  if (midur < hidur) {
                    tmpitems[hindx] = tmpitem;
                    tmpmodes[hindx] = leg123mode;
                    midurs[hindx] = midur;
                  }
                  durlim = hidur;
                  warncc(durlim != hi32 && durlim > 65534,Exit|msgtid,"durlim %u at %u exceeds 64k",durlim,cntlimdur);
                  error_eq(durlim,hi32);
                }

                if (no_airsep || air) continue;

                // ground-only
                // todo: change into reserved versus unreserved to accomodate fare availability
                if (durcntgnd == 0) {
                  midursgnd[0] = midur;
                  tmpitemsgnd[0] = tmpitem;
                  durcntgnd = 1;
                } else if (durcntgnd < cntlimdur) {
                  tmpitemsgnd[durcntgnd] = tmpitem;
                  midursgnd[durcntgnd++] = midur;
                } else {
                  hidur = hindx = 0;
                  for (durndx = 0; durndx < cntlimdur; durndx++) {
                    if (midursgnd[durndx] > hidur) { hidur = midursgnd[durndx]; hindx = durndx; }
                  }
                  durlimgnd = hidur;
                  error_eq(durlimgnd,hi32);
                  if (midur < hidur) {
                    midursgnd[hindx] = midur;
                    tmpitemsgnd[hindx] = tmpitem;
                  }
                }

              } // each v3
            } // each v2
          } // each v1

          if (n123 == var12limit) stat_var12lim++;
        } // each mid2
      } // each mid1

      if (altcnt > hialt) { hialt = altcnt; altdep = dep; altarr = arr; }

      error_gt(durcnt,varlimlh,dep);

      if (durcnt == cntlimdur) stat_partlimdur++;
      else if (durcnt > cntlimdur) {
        warn(msgtid,"durlim %u above varlimit %u/%u",durlim,cntlimdur,varlimit);
        durcnt = cntlimdur;
      }

      warncc(durlim != hi32 && durlim > 65534,Exit|msgtid,"durlim %u exceeds 64k",durlim);
      warncc(durlimgnd != hi32 && durlimgnd > 65534,Exit|msgtid,"durlim %u exceeds 64k",durlimgnd);

      if (durcnt == 0) { nogen++; continue; }

      iadrinc(cnts,dep,arr,tid);
      outcnt++;

      // emit mixed tmpitems only, or best half of tmpitems and -gnd if needed
      aircnt = 0;
      for (n = 0; n < durcnt; n++) {
        if (tmpmodes[n] & Airbit) aircnt++;
      }
      if (no_airsep || aircnt * 2 <= cntlimdur) { // mixed only

        gen = durcnt;

        for (n = 0; n < durcnt; n++) {
          if (midurs[n] == hi32) { warn(0,"dep %u arr %u no midur at %u",dep,arr,n); break; }
          tmpitem = tmpitems[n];
          if (wriadr8(lstitems,dep,arr * varlimit + n,tmpitem)) break;
        }
        if (n < durcnt) continue;
        if (wriadr2(precnts,dep,arr,(ub2)n)) continue;
        lstlen += n;
        continue;
      }

      // best half of each
      for (n = 0; n < durcnt; n++) sortdurs[n] = (midurs[n] << 16) | n;
      sort4(sortdurs,durcnt,FLN,"net2 midurs");
      n = gen = 0;
      while (n < durcnt && gen < cntlimdur / 2) {
        hindx = sortdurs[gen] & hi16;
        error_ge(hindx,durcnt);
        tmpitem = tmpitems[hindx];
        if (midurs[hindx] == hi32) { warn(0,"dep %u arr %u no midur at %u",dep,arr,n); n = 0; break; }
        if (wriadr8(lstitems,dep,arr * varlimit + gen,tmpitem)) { n = 0; break; }
        gen++;
      }
      if (n == 0) continue;
      lstlen += gen;

      if (durcntgnd == 0) {
        wriadr2(precnts,dep,arr,(ub2)gen);
        continue;
      }

      for (n = 0; n < durcntgnd; n++) sortdurs[n] = (midursgnd[n] << 16) | n;
      sort4(sortdurs,durcntgnd,FLN,"net2 midurs");

      n = 0;
      while (n < durcntgnd && gen < cntlimdur) {
        hindx = sortdurs[n] & hi16;
        error_ge(hindx,durcntgnd);
        tmpitem = tmpitemsgnd[hindx];
        if (midursgnd[hindx] == hi32) { warn(0,"dep %u arr %u no midur at %u",dep,arr,n); n = 0; break; }
        if (wriadr8(lstitems,dep,arr * varlimit + gen,tmpitem)) { n = 0; break; }
        gen++;
      }
      if (n == 0) continue;
      lstlen += gen;
      if (wriadr2(precnts,dep,arr,(ub2)gen)) continue;

    } // each arrival port

    sumoutcnt += outcnt;
  } // each departure port

  ub8 allestdur = stat_estdur + stat_noestdur;
  info(msgtid|CC0,"no estdur \ah%lu of \ah%lu = \ap%lu%lu",stat_noestdur,allestdur,stat_noestdur,allestdur);

  estdur3_stats(tid);

  info(msgtid,"limits dist \ah%lu \ah%lu \ah%lu \ah%lu  net1 \ah%lu time \ah%lu,\ah%lu var \ah%lu",
    stat_distlim1,stat_distlim2,stat_distlim3,stat_distlim4,stat_net1lim,stat_timlim,stat_timlim2,stat_var12lim);
  info(msgtid,"  var \ah%lu lotx \ah%lu",stat_varlim,stat_lotx);
  info(msgtid,"  da1 \ah%lu da2 \ah%lu da3 \ah%lu",stat_da1,stat_da2,stat_da3);

  info(msgtid,"thread %u 2-stop pass 2 done \ah%lu triplets in \ah%lu pairs, \ah%lu nogen",tid,lstlen,sumoutcnt,nogen);

  pdep = ports + altdep;
  parr = ports + altarr;
  info(0,"high alt %u for %u-%u %s %s",hialt,altdep,altarr,pdep->iname,parr->iname);

  argp->lstlen = lstlen;

  return info(msgtid,"end in thread %u",tid);
} // 2-stop pass 2

static void *net2_pass2(void *vp)
{
  struct net2_p2_args *argp = (struct net2_p2_args *)vp;
  ub4 tid = argp->tid;
  globs.tids[tid] = 1;
  ub4 msgtid = (tid << Tidshift) | Tidbit;
  if (argp->nice) {
    ossetprio(argp->nice);
    info(msgtid,"nice value %d",argp->nice);
  }
  int rv = net2_pas2(argp);
  argp->rv = rv;
  rmthtimer(argp->tid);
  globs.tids[tid] = 0;
  return vp;
}

// create 2-stop connectivity matrix and derived info
// uses 2 via's from 0-stop net
int mknet2(struct network *net,ub4 varlimit,ub4 var12limit,ub4 cntonly,ub4 netstop)
{
  ub4 nstop = 2;
  ub4 portcnt = net->portcnt;
  ub4 hopcnt = net->hopcnt;
  ub4 thopcnt = net->thopcnt;
  ub4 whopcnt = net->whopcnt;
  struct port *ports,*pmid,*pdep,*parr;
  block *lstblk;
  ub4 *portsbyhop;
  iadrbase *cnts,*cnts0,*cnts1,*precnts;
  iadrbase *conofs;
  ub4 *portdst;
  ub8 ofs,ofs1,ofs2,ofs3,endofs;
  ub4 *lst,*newlst,*lstv1,*lst1,*lst2,*lst3;
  ub4 *hopdist = net->hopdist;
  ub4 dep,mid1,mid2,arr;
  ub4 dmid1,dmid2;
  ub4 iv;
  ub4 cnt,n1,n2,v1,v2,v3,leg,leg1,leg2,leg3,nleg;
  ub8 lstlen,newlstlen,tlstlen;
  ub4 dist1,dir;
  ub4 maxwalk1,maxwalk2,maxwalk3,sumwalkdist1,sumwalkdist2,sumwalkdist3,walkdist1,walkdist2,walkdist3;
  ub4 gen;
  ub4 midur;
  ub4 stat_nocon = 0,stat_partcnt = 0,stat_cntlim = 0,stat_partlimdur = 0;

  struct eta eta;

  if (varlimit == 0) return warn0(0,"skip 2-stop net on zero limit");

  error_zz(portcnt,hopcnt);

  info(0,"init %u/%u stop connections for %u port \ah%u hop network",nstop,netstop,portcnt,whopcnt);

  info(0,"limits: var %u var12 %u",varlimit,var12limit);

  ports = net->ports;

  portsbyhop = net->portsbyhop;

  precnts = &net->conipos;
  clear(precnts);
  cnts = net->concnt + nstop;
  conofs = net->conofs + nstop;

  block *lstblk0 = net->conlst;
  ub4 *conlst1 = blkdata(lstblk0,0,ub4);
  iadrbase *conofs0 = net->conofs;

  ub4 sparsethres = net->sparsethres;
  ub4 lowcon = globs.net2con[0];
  ub4 distabove_da = globs.net2above;
  ub4 distabove_da1 = distabove_da * 2;

  int net1 = (net->lstlen[1] != 0);

  // main net2 structure
  if (mkiadr0(precnts,portcnt,portcnt,ub2,sparsethres,12,"net2 precnts")) return 1;
  if (setiadropts(precnts,Iadr_softlim)) return 1;

  if (mkiadr0(cnts,portcnt,portcnt,ub2,sparsethres,12,"net2 cnts")) return 1;
  if (mkiadr0(conofs,portcnt,portcnt,ub8,sparsethres,12,"net2 ofs")) return 1;

  iadrbase *durlims = net->durlims + 2;
  iadrbase *durlims1 = net->durlims + 1;

  iadrbase *lstitems = &net->lst2items;

  if (mkiadr0(durlims,portcnt,portcnt,ub2,sparsethres,12,"net2 durlims")) return 1;

  ub8 lstitem;

  error_lt(varlimit,globs.net2limit[0]);
  error_lt(varlimit,globs.net2limit[1]);
  error_ne(varlimit,globs.net2limit[2]);
  if (mkiadr0(lstitems,portcnt,portcnt * varlimit,ub8,sparsethres,32,"net2 lstitems")) return 1;
  if (setiadropts(lstitems,Iadr_append | Iadr_softlim)) return 1;

  portdst = talloc(portcnt, ub4,0,"net portdst",portcnt);  // outbound conn stats

  error_zp(hopdist,0);

  nleg = nstop + 1;

/* Essentially we do for each (departure,arrival) pair:
   Search for 2 'via' ports such that trip (dep,via1), (via1,via2) and (via2,arr) exist
   Trim list of alternatives based on typical trip duration
   Store result by value. This is memory-intensive but keeps code simple

   In short:
   foreach dep
     foreach arr
       foreach mid1 with [dep,mid1]
         foreach mid2 with [mid1,mid2] and [mid2,arr]
           ...

*/

/*
  pass 1 : foreach (dep,arr) pair at this #stops:
  bound overall best and worst
  create histogram and derive threshold to use as filter in next pass
  estimate size of trip list matrix
  obtain basic stats
*/

  ub8 dupstats[16];

  lstlen = 0;

  aclear(dupstats);

  // prepare mid1 and 2 lookup info
  ub4 *dmid1s,*depmid1s = talloc(portcnt * Viacnt2,ub4,0,"net depdmid",Viacnt2);
  ub4 *dmid1durs,*depmid1durs = talloc(portcnt * Viacnt2,ub4,0,"net depdmid",Viacnt2);
  ub4 *dmid1ds,*depmid1ds = talloc(portcnt * Viacnt2,ub4,0,"net depdmidd",Viacnt2);
  ub4 *dmid2s,*arrmid2s = talloc(portcnt * Viacnt2,ub4,0,"net arrdmid",Viacnt2);
  ub4 *dmid2ds,*arrmid2ds = talloc(portcnt * Viacnt2,ub4,0,"net arrdmidd",Viacnt2);
  ub4 *dmid1acnt,*depmid1cnts = talloc(portcnt * Viacnt2,ub4,0,"net depdmid",Viacnt2);
  ub4 *dmid2acnt,*arrmid2cnts = talloc(portcnt * Viacnt2,ub4,0,"net arrmid",Viacnt2);

  ub4 dmid1cnt,*dmid1cnts = talloc(portcnt,ub4,0,"net depdmidcnt",portcnt);
  ub4 dmid2cnt,*dmid2cnts = talloc(portcnt,ub4,0,"net depdmidcnt",portcnt);

  cnts0 = net->concnt;

  cnts1 = net->concnt + 1;

  ub4 dmidbins[Viacnt2];
  ub4 dmidivs = Elemcnt(dmidbins) - 1;

  ub4 depcnt0,arrcnt0,depofs,arrofs,ddmid1,ddmid2;
  ub4 *dlst,*alst,*dlstdur;
  ub4 *depdurlst0 = net->depdurlst[0];
  aclear(dmidbins);
  ub4 ddep,*deplst0 = net->deplst[0];
  ub4 *arrlst0 = net->arrlst[0];

  // prepare via 1
  ub4 fltdepcnt = 0,fltarrcnt = 0;

  for (dep = 0; dep < portcnt; dep++) {

    if (progress0(&eta,"2-stop pass 0 dep %u of %u",dep,portcnt)) return 1;

    pdep = ports + dep;
    if (pdep->valid == 0) continue;

    depcnt0 = pdep->depcnt[0];
    if (depcnt0 == 0) { info(0,"port %u no deps %s",dep,pdep->iname); continue; }
    depofs = pdep->depofs[0];
    error_gt(depofs + depcnt0,net->pairs[0],dep);
    dlst = deplst0 + depofs;
    dlstdur = depdurlst0 + depofs;

    dmid1s = depmid1s + dep * Viacnt2;
    dmid1durs = depmid1durs + dep * Viacnt2;
    dmid1ds = depmid1ds + dep * Viacnt2;
    dmid1acnt = depmid1cnts + dep * Viacnt2;
    dmid1 = 0;
    for (ddmid1 = 0; ddmid1 < depcnt0 && dmid1 < Viacnt2; ddmid1++) {
      ddep = dlst[ddmid1];

      mid1 = ddep & Nbrmask;
      if ( (ddep & Viabit) == 0 && (ddep & Tripbits) != Tripbits ) continue;

      pmid = ports + mid1;
      if (pmid->valid == 0) continue;

      n1 = rdiadr2(cnts0,dep,mid1);
      error_z(n1,mid1);
      dir = fgeodist(pdep,pmid,1);
      dmid1ds[dmid1] = dir;

      dmid1acnt[dmid1] = min(n1,Lst2vmask);
      dmid1durs[dmid1] = dlstdur[ddmid1];
      dmid1s[dmid1++] = mid1;
    }
    dmid1cnts[dep] = dmid1;
    dmidbins[min(dmid1,dmidivs)]++;
    if (dmid1 == Viacnt2) {
      fltdepcnt++;
      info(Iter,"dep %u limiting mid1 to %u %s",dep,dmid1,pdep->iname);
    }
  }

  for (iv = 0; iv <= dmidivs; iv++) { dmid1 = dmidbins[iv]; infocc(dmid1,Notty,"dmids 1 %u: \ah%u",iv,dmid1); }
  aclear(dmidbins);

  // prepare via 2
  for (arr = 0; arr < portcnt; arr++) {

    if (progress0(&eta,"2-stop pass 0 arr %u of %u",arr,portcnt)) return 1;

    parr = ports + arr;
    if (parr->valid == 0) continue;

    arrcnt0 = parr->arrcnt[0];
    if (arrcnt0 == 0) { info(0,"port %u no arrs %s",dep,parr->iname); continue; }
    arrofs = parr->arrofs[0];
    alst = arrlst0 + arrofs;

    dmid2s = arrmid2s + arr * Viacnt2;
    dmid2ds = arrmid2ds + arr * Viacnt2;
    dmid2acnt = arrmid2cnts + arr * Viacnt2;
    dmid2 = 0;
    for (ddmid2 = 0; ddmid2 < arrcnt0 && dmid2 < Viacnt2; ddmid2++) {
      ddep = alst[ddmid2];
      mid2 = ddep & Nbrmask;

      if ( (ddep & Viabit) == 0 && (ddep & Tripbits) != Tripbits ) continue;

      if (mid2 == arr) continue;
      pmid = ports + mid2;
      if (pmid->valid == 0) continue;

      n2 = rdiadr2(cnts0,mid2,arr);
      if (n2 == 0) continue;

      dir = fgeodist(pmid,parr,1);
      dmid2ds[dmid2] = dir;

      dmid2acnt[dmid2] = min(n2,Lst2vmask);
      dmid2s[dmid2++] = mid2;
    }
    dmid2cnts[arr] = dmid2;
    dmidbins[min(dmid2,dmidivs)]++;
    if (dmid2 == Viacnt2) {
      fltarrcnt++;
      info(Iter,"arr %u limiting mid2 to %u %s",arr,dmid2,parr->iname);
    }
  }
  for (iv = 0; iv <= dmidivs; iv++) { dmid2 = dmidbins[iv]; infocc(dmid2,Notty,"dmids 2 %u: \ah%u",iv,dmid2); }

  info(CC0,"%u dep limited on %u vias",fltdepcnt,Viacnt2);
  info(CC0,"%u arr limited on %u vias",fltarrcnt,Viacnt2);

  // prepare thread chunks
  // aim at twice the number of cores (rely on config)
  // half of these run at low prio, to support unequal load
  // divide the <dep,arr> matrix equally on dep and align on iadr
  // so each cell is accessed by a single thread
  // all allocation is done around it
  // main thread takes chunk 0 and possible slack
  ub4 depfrom,depchunk;
  int rv;
  void *trv;

  struct net2_p2_args *argp,*argp0,*argp1,*targs = talloc(Nthread+1,struct net2_p2_args,0,"net2 tidargs",0);
  pthread_t ptids[Nthread];
  pthread_attr_t thrattr;

  argp0 = targs;
  argp1 = targs + Nthread;  // for last partial;

  ub4 tid = 0;

  ub4 tidcnt,btidcnt;

  if (portcnt > 1000) {
    btidcnt = globs.tidcnt;
    tidcnt = btidcnt == 1 ? 1 : btidcnt * 2;
  } else tidcnt = btidcnt = 1;

  argp0->tid = tid;
  argp0->tidcnt = tidcnt;
  argp0->net = net;
  argp0->depfrom = 0;
  argp0->depto = portcnt;

  argp0->varlimit = varlimit;
  argp0->var12limit = var12limit;
  argp0->cntonly = cntonly;
  argp0->lowcon = lowcon;
  argp0->net1 = net1;
  argp0->distabove_da = distabove_da;
  argp0->distabove_da1  = distabove_da1;

  argp0->depmid1s = depmid1s;
  argp0->depmid1durs = depmid1durs;
  argp0->depmid1ds = depmid1ds;
  argp0->depmid1cnts = depmid1cnts;
  argp0->dmid1cnts = dmid1cnts;

  argp0->arrmid2s = arrmid2s;
  argp0->arrmid2ds = arrmid2ds;
  argp0->arrmid2cnts = arrmid2cnts;
  argp0->dmid2cnts = dmid2cnts;

  if (tidcnt == 1) {
    argp0->tidcnt = 1;
    rv = net2_pas1(argp0);
    if (rv) { warn(0,"pass 1 returned %d",rv); return rv; }
  } else {
    depchunk = (portcnt / tidcnt) & (~Maxmask);
    info(0,"%u threads, %u ports in chunks of %u",tidcnt,portcnt,depchunk);

    argp0->depto = min(depchunk,portcnt);
    depfrom = depchunk;

    for (tid = 1; tid < tidcnt && depfrom < portcnt - 1; tid++) {
      argp = targs + tid;
      *argp = *argp0;
      argp->tid = tid;
      argp->depfrom = depfrom;
      argp->depto = min(depfrom + depchunk,portcnt);
      depfrom += depchunk;
    }

    if (depfrom < portcnt - 1) {  // last partial chunk
      *argp1 = *argp0;
      argp1->depfrom = depfrom;
      argp1->depto = portcnt;
      info(0,"running ports %u-%u",argp1->depfrom,argp1->depto);
      if (net2_pas1(argp1)) return error(0,"net2 pass 1 partial chunk %u-%u failed",depfrom,portcnt);
    }

    // todo: move to system header/module
    if (pthread_attr_init(&thrattr)) return oserror0(0,"cannot init pthread attrs");
    if (pthread_attr_setinheritsched(&thrattr,PTHREAD_EXPLICIT_SCHED)) oswarn0(0,"cannot init pthread attrs");

#ifdef SCHED_BATCH
    if (pthread_attr_setschedpolicy(&thrattr,SCHED_BATCH)) oswarn0(0,"cannot init pthread attrs");
#endif

    for (tid = 1; tid < tidcnt; tid++) {
      argp = targs + tid;
      if (argp->depto == 0) continue;

#ifdef SCHED_IDLE
      if (tid == btidcnt) {
        if (pthread_attr_setschedpolicy(&thrattr,SCHED_IDLE)) oswarn0(0,"cannot init pthread attrs");
      }
#endif
      if (tid >= btidcnt) argp->nice = 10;

      dep = argp->depfrom;
      arr = argp->depto;
      pdep = ports + dep;
      parr = ports + arr;

      info(0,"creating thread %u: ports %u-%u %s - %s",tid,dep,arr,pdep->iname,parr->iname);
      rv = pthread_create(ptids + tid,&thrattr,&net2_pass1,argp);
      if (rv) return oserror(0,"cannot create thread %u",tid);
      info(0,"created thread %u",tid);
    }

    // first chunk in main thread
    info(0,"running ports %u-%u",argp0->depfrom,argp0->depto);
    net2_pass1(argp0);
    rv = argp0->rv;
    if (rv == 2) return 1;
    else if (rv) return error(0,"net2 pass 1 chunk %u-%u failed",0,depchunk);
    tlstlen = targs->lstlen;

    for (tid = 1; tid < tidcnt; tid++) {
      argp = targs + tid;
      if (argp->depto == 0) continue;
      info(0,"joining thread %u",tid);
      if (pthread_join(ptids[tid],&trv)) return oserror(0,"cannot join thread %u",tid);
      if (trv == NULL) return error(0,"thread %u returned nil error",tid);
      argp = (struct net2_p2_args *)trv;
      rv = argp->rv;
      if (rv) return error(0,"thread %u returned error %d",tid,rv);
      tlstlen += argp->lstlen;
      info(0,"joined thread %u",tid);
    }
    info(Emp,"2-stop pass 1 \ah%lu tentative triplets",tlstlen);
  }

  // pass 2
  mkiadr1(precnts);
  mkiadr1(lstitems);

  lstlen = 0;

  ub4 nogen = 0;

  if (tidcnt == 1) {
    rv = net2_pas2(argp0);
    if (rv) return rv;
  } else {

    if (argp1->depto) {  // last partial chunk
      if (net2_pas2(argp1)) return error(0,"net2 pass 2 partial chunk %u-%u failed",argp1->depfrom,portcnt);
    }

#ifdef SCHED_BATCH
    if (pthread_attr_setschedpolicy(&thrattr,SCHED_BATCH)) oswarn0(0,"cannot init pthread attrs");
#endif

    for (tid = 1; tid < tidcnt; tid++) {
      argp = targs + tid;
      if (argp->depto == 0) continue;

#ifdef SCHED_IDLE
      if (tid == btidcnt) {
        if (pthread_attr_setschedpolicy(&thrattr,SCHED_IDLE)) oswarn0(0,"cannot init pthread attrs");
      }
#endif

      info(0,"creating thread %u: ports %u-%u",tid,argp->depfrom,argp->depto);
      rv = pthread_create(ptids + tid,&thrattr,&net2_pass2,argp);
      if (rv) return oserror(0,"cannot create thread %u",tid);
      info(0,"created thread %u",tid);
    }

    // first chunk in main thread
    net2_pass2(argp0);
    rv = argp0->rv;
    if (rv == 2) return 1;
    else if (rv) return error(0,"net2 pass 2 chunk %u-%u failed",0,argp0->depto);

    for (tid = 1; tid < tidcnt; tid++) {
      argp = targs + tid;
      if (argp->depto == 0) continue;
      info(0,"joining thread %u",tid);
      if (pthread_join(ptids[tid],&trv)) return oserror(0,"cannot join thread %u",tid);
      if (trv == NULL) return error(0,"thread %u returned nil error",tid);
      argp = (struct net2_p2_args *)trv;
      rv = argp->rv;
      if (rv) return error(0,"thread %u returned error %d",tid,rv);
      info(0,"joined thread %u",tid);
    }
    pthread_attr_destroy(&thrattr);
  }

  ofs = 0;

  for (dep = 0; dep < portcnt; dep++) {

    if (progress(&eta,"2-stop pass 2b port %u of %u  \ah%lu conns",dep,portcnt,ofs)) return 1;

    for (arr = 0; arr < portcnt; arr++) {
      if (arr == dep) continue;

      gen = rdiadr2(precnts,dep,arr);
      if (gen == 0) continue;

      ofs += gen;
    }
  }
  lstlen = ofs;

  for (iv = 0; iv < Elemcnt(dupstats); iv++) if (dupstats[iv]) info(0,"dup %u: \ah%lu",iv,dupstats[iv]);

  info(Emp,"pass 2 %u stop done, \ah%lu triplets, \ah%u filtered",nstop,lstlen,nogen);

  if (net1) rmiadr(durlims1);

  for (iv = 0; iv <= dmidivs; iv++) if (dmidbins[iv] > 64) info(0,"dmids %u: \ah%u",iv,dmidbins[iv]);

  warncc(lstlen == 0,0,"no connections at %u-stop for %u ports",nstop,portcnt);
  if (lstlen == 0) return 0;

  ub4 cnt1,cnt0,newcnt;
  struct range portdr;
  ub4 ivportdst[32];
  mkhist(caller,portdst,portcnt,&portdr,Elemcnt(ivportdst),ivportdst,"outbounds by port",Info);

  ub4 genstats[64];
  ub4 cntstats[64];
  ub4 geniv = 63;

  aclear(cntstats);
  aclear(genstats);

  mkiadr1(cnts);

  cpiadr(conofs,cnts);
  mkiadr1(conofs);

  cpiadr(durlims,cnts);
  mkiadr1(durlims);

  // prepare list matrix

  lstblk = net->conlst + nstop;

  lst = mkblock(lstblk,lstlen * nleg,ub4,Noinit,"net2 %u-stop conlst",nstop);

  ub1 *modes = alloc(lstlen,ub1,0,"net2 modes",0);
  ub1 *hopmode = net->hopmodes;

  ofs = newcnt = 0;

  if (portcnt < 20000) {
    for (dep = 0; dep < portcnt; dep++) {
      for (arr = 0; arr < portcnt; arr++) {
        if (dep == arr) continue;
        cnt = rdiadr2(precnts,dep,arr);
        if (net->lstlen[1]) cnt1 = rdiadr2(cnts1,dep,arr);
        else cnt1 = 0;
        cnt0 = rdiadr2(cnts0,dep,arr);
        if (cnt) {
          ofs += cnt;
          if (cnt1 == 0 && cnt0 == 0) newcnt++;
        }
      }
    }
    info(0,"\ah%u new connections",newcnt);
    error_ne(ofs,lstlen);
  }

  aclear(dupstats);

  ub8 dursort[Durcnt];
  ub4 *tmpv1,tmplst[Durcnt * 3];
  ub1 tmpmodes[Durcnt];
  ub4 idx,idx2,n;
  ub4 pairs = 0;

  // pass 3: fill from pass 2 counts, limits and legs
  ofs = 0;
  for (dep = 0; dep < portcnt; dep++) {

    if (progress(&eta,"2-stop pass 3 port %u of %u  \ah%lu conns",dep,portcnt,ofs)) return 1;

    pdep = ports + dep;

    if (pdep->valid == 0) continue;

    dmid1s = depmid1s + dep * Viacnt2;
    dmid1acnt = depmid1cnts + dep * Viacnt2;
    dmid1cnt = dmid1cnts[dep];

    if (dmid1cnt == 0) continue;

    endofs = ofs;

    if (pairs >= hi32 - portcnt) {
      warn(0,"limiting pairs to \ah%u at dep %u",pairs,dep);
      break;
    }

    for (arr = 0; arr < portcnt; arr++) {
      endofs = ofs;
      if (arr == dep) continue;

      cnt = rdiadr2(precnts,dep,arr);
      if (cnt == 0) continue;
      cnt = min(cnt,Durcnt);
      parr = ports + arr;

      error_z(parr->valid,arr);

      dmid2s = arrmid2s + arr * Viacnt2;
      dmid2acnt = arrmid2cnts + arr * Viacnt2;
      dmid2cnt = dmid2cnts[arr];

      gen = 0; // generate final count

      if (wriadr8(conofs,dep,arr,ofs)) return 1;

      lstv1 = lst + ofs * nleg;
      error_ge(ofs,lstlen);
      tmpv1 = tmplst;

      endofs = ofs + cnt - 1;

      if (endofs >= lstlen) {
        warn(0,"limiting net2 to \ah%lu at dep %u of %u",endofs,dep,portcnt);
        break;
      }

      for (n = 0; n < cnt; n++) {
        lstitem = rdiadr8(lstitems,dep,arr * varlimit + n);

        dmid1 = lstitem & Lst2mmask;
        error_ge(dmid1,dmid1cnt);
        mid1 = dmid1s[dmid1];

        dmid2 = (lstitem >> Lst2m2shift) & Lst2mmask;
        error_ge(dmid2,dmid2cnt);
        mid2 = dmid2s[dmid2];

        v1 = (lstitem >> Lst2v1shift) & Lst2vmask;
        v2 = (lstitem >> Lst2v2shift) & Lst2vmask;
        v3 = (lstitem >> Lst2v3shift) & Lst2vmask;

        midur = (ub2)(lstitem >> Lst2durshift);

        if (midur == 0 || midur >= 65534) {
          warn(0,"port %u-%u var %u dur %u",dep,arr,n,midur);
          continue;
        }

        ofs1 = rdiadr8(conofs0,dep,mid1);
        lst1 = conlst1 + ofs1;

        ofs2 = rdiadr8(conofs0,mid1,mid2);
        lst2 = conlst1 + ofs2;

        ofs3 = rdiadr8(conofs0,mid2,arr);
        lst3 = conlst1 + ofs3;

        leg1 = lst1[v1];
        leg2 = lst2[v2];
        leg3 = lst3[v3];

        if (leg1 >= whopcnt || leg2 >= whopcnt || leg3 >= whopcnt) {
          warn(0,"dep %u arr %u invalid legs",dep,arr);
          continue;
        }
        if (portsbyhop[leg1 * 2] != dep) {
          error(0,"hop %u %u-%u vs %u arr %u",leg1,portsbyhop[leg1 * 2],portsbyhop[leg1 * 2 + 1],dep,arr);
          continue;
        }

        dist1 = hopdist[leg1];
        if (leg1 >= thopcnt) {
          walkdist1 = maxwalk1 = sumwalkdist1 = dist1;
        } else walkdist1 = sumwalkdist1 = maxwalk1 = 0;

        sumwalkdist2 = sumwalkdist1;
        walkdist2 = walkdist1;
        maxwalk2 = maxwalk1;

        if (leg2 >= thopcnt) {
          walkdist2 += hopdist[leg2];
          sumwalkdist2 += hopdist[leg2];
          maxwalk2 = max(maxwalk2,walkdist2);
        } else walkdist2 = 0;

        if (portsbyhop[leg3 * 2 + 1] != arr) {
          error(0,"hop %u %u-%u vs %u arr %u",leg3,portsbyhop[leg3 * 2],portsbyhop[leg3 * 2 + 1],dep,arr);
          continue;
        }

        sumwalkdist3 = sumwalkdist2;
        walkdist3 = walkdist2;
        maxwalk3 = maxwalk2;

        if (leg3 >= thopcnt) {
          walkdist3 += hopdist[leg3];
          sumwalkdist3 += hopdist[leg3];
          maxwalk3 = max(maxwalk3,walkdist3);
        }

        if (gen >= Elemcnt(dursort)) {
          warn(0,"port %u-%u gen %u >= %lu",dep,arr,gen,Elemcnt(dursort));
          continue;
        }
        dursort[gen] = (ub8)midur << 32 | gen;
        tmpmodes[gen] = hopmode[leg1] | hopmode[leg2] | hopmode[leg3];

        error_ovf(maxwalk3,ub2);
        error_ovf(sumwalkdist3,ub2);

        error_gt((ub8)(tmpv1 + 3),(ub8)(tmplst + Elemcnt(tmplst)),gen);
        tmpv1[0] = leg1;
        tmpv1[1] = leg2;
        tmpv1[2] = leg3;

        if (checktrip3(net,tmpv1,nleg,dep,arr,mid1,hopdist[leg1] + hopdist[leg2] + hopdist[leg3])) continue;

        gen++;
        tmpv1 += nleg;
      } // each var in varlimit

      if (gen < cnt) {
        stat_partcnt++;
      }

      genstats[min(gen,geniv)]++;
      cntstats[min(cnt,geniv)]++;

      // none found for any dep-Mid-arr, but mid exists : no events
      if (cnt && gen == 0) stat_nocon++;

      if (gen == 0) continue;

      pairs++;

      if (gen > cnt) {
        warn(0,"port %u-%u gen %u cnt %u",dep,arr,gen,cnt);
        continue;
      }

      if (gen > 1) fsort8(dursort,gen,0,FLN,"nstop durlist");
      midur = (ub4)(dursort[0] >> 32);
      for (idx = 0; idx < gen; idx++) {
        idx2 = dursort[idx] & hi32;
        if (idx2 > gen) {
          warn(0,"port %u-%u idx %u gen %u",dep,arr,idx2,gen);
          break;
        }
        memcpy(lstv1,tmplst + idx2 * nleg,nleg * sizeof(ub4));
        modes[ofs + idx] = tmpmodes[idx2];
        lstv1 += nleg;
      }
      if (idx < gen) continue;

      ofs += gen;
      if (wriadr2(cnts,dep,arr,(ub2)gen)) return 1;
      if (wriadr2(durlims,dep,arr,(ub2)midur)) return 1;

    } // each arrival port

    if (endofs >= lstlen) break;

  } // each departure port

  afree(depmid1s,"net");
  afree(depmid1durs,"net");
  afree(depmid1ds,"net");
  afree(arrmid2s,"net");
  afree(arrmid2ds,"net");
  afree(depmid1cnts,"net");
  afree(arrmid2cnts,"net");

  newlstlen = ofs;
  if (newlstlen > lstlen) {
    error(0,"newlst %lu lst %lu",newlstlen,lstlen);
    newlstlen = lstlen;
  }

  rmiadr(lstitems);
  rmiadr(precnts);

  finiadr(conofs);

  ub8 conperc = (100UL * pairs) / ((ub8)portcnt * portcnt);
  info(Emp,"pass 3 net %u done, \ah%lu from \ah%lu triplets in \ah%u pairs %lu%%",nstop,newlstlen,lstlen,pairs,conperc);

  if (lstlen - newlstlen > 1024 * 1024 * 128) {
    info(0,"trim from \ah%lu to \ah%lu",lstlen,newlstlen);
    newlst = trimblock(lstblk,newlstlen * nleg,ub4);
  } else newlst = lst;

  net->lstlen[nstop] = newlstlen;
  net->pairs[nstop] = pairs;

  infocc(newlstlen > 1024 * 1024 * 256,0,"checking %u hops",whopcnt);
  for (ofs = 0; ofs < newlstlen * nleg; ofs++) {
    leg = newlst[ofs];
    error_ge(leg,whopcnt);
  }
  infocc(newlstlen > 1024 * 1024 * 256,0,"checking %u modes",whopcnt);
  for (ofs = 0; ofs < newlstlen; ofs++) {
    error_z(modes[ofs],ofs);
  }

  for (iv = 0; iv < Elemcnt(dupstats); iv++) if (dupstats[iv]) info(0,"dup %u: \ah%lu",iv,dupstats[iv]);

  info(0,"no conn %u  partcnt %u  cntlim %u partlim1 %u",stat_nocon,stat_partcnt,stat_cntlim,stat_partlimdur);

  for (iv = 0; iv <= geniv; iv++) infocc(cntstats[iv],V0,"%u: gen \ah%u cnt \ah%u",iv,genstats[iv],cntstats[iv]);

  net->modes[nstop] = modes;

  // verify all triplets
  for (dep = 0; portcnt < 150000 && dep < portcnt; dep++) {
    if (progress0(&eta,"verify trips port %u of %u",dep,portcnt)) return 1;
    for (arr = 0; arr < portcnt; arr++) {
      if (dep == arr) continue;
      n1 = rdiadr2(cnts,dep,arr);
      if (n1 == 0) continue;
      ofs = rdiadr8(conofs,dep,arr);
      lstv1 = newlst + ofs * nleg;
      for (v1 = 0; v1 < n1; v1++) {
        if (checktrip(net,lstv1,nleg,dep,arr,hi32)) {
          wriadr2(cnts,dep,arr,0);
          break;
        }
        lstv1 += nleg;
      }
    }
  }
  finiadr(cnts);

  // prepare sorted outbounds and inbounds per port for search
  ub4 depcnt,arrcnt,viacnt,darr,dvia,via;
  ub4 *deplst = alloc(pairs,ub4,0,"net2 deplst",0);
  ub4 *arrlst = alloc(pairs,ub4,0,"net2 arrlst",0);
  ub4 *depdurlst = alloc(pairs,ub4,0,"net2 deplst",0);
  ub4 *arrdurlst = alloc(pairs,ub4,0,"net2 deplst",0);

  ub8 *dasort = talloc(portcnt,ub8,0,"net0 depsort",0);
  ub4 daofs,vaofs;

  ub1 *arrmap = talloc0(portcnt,ub1,0);
  ub4 cumviacnt = 0;

  ofs = 0;

  for (dep = 0; dep < portcnt; dep++) {
    if (progress0(&eta,"dep conlst port %u of %u",dep,portcnt)) return 1;
    pdep = ports + dep;
    if (pdep->valid == 0) continue;
    if (ofs >= pairs) {
      warn(0,"skip port %u on ofs %lu above pairs",dep,ofs);
      continue;
    }
    pdep->depofs[nstop] = (ub4)ofs;
    depcnt = 0;
    for (arr = 0; arr < portcnt; arr++) {
      if (dep == arr) continue;
      parr = ports + arr;
      if (parr->valid == 0) continue;
      cnt = rdiadr2(cnts,dep,arr);
      if (cnt == 0) continue;
      midur = rdiadr2(durlims,dep,arr);
      dasort[depcnt] = (ub8)midur << 32 | arr;
      depcnt++;
    }
    pdep->depcnt[nstop] = depcnt;

    if (depcnt > 1) fsort8(dasort,depcnt,0,FLN,"net2 deplst");
    else if (depcnt == 0) continue;
    error_gt(ofs + depcnt,pairs,depcnt);
    for (darr = 0; darr < depcnt; darr++) {
      arr = dasort[darr] & hi32;
      midur = (ub4)(dasort[darr] >> 32);
      deplst[ofs+darr] = arr;
      depdurlst[ofs+darr] = midur;
    }
    ofs += depcnt;
  }

  // prepare dep via list
  for (dep = 0; dep < portcnt; dep++) {
    if (progress0(&eta,"dep vialst port %u of %u",dep,portcnt)) return 1;
    pdep = ports + dep;
    if (pdep->valid == 0) continue;
    daofs = pdep->depofs[2];
    depcnt = pdep->depcnt[2];
    nclear(arrmap,portcnt);
    arrmap[dep] = 1;
    for (darr = 0; darr < depcnt; darr++) {
      arr = deplst[daofs + darr] & Nbrmask;
      cnt = rdiadr2(cnts,dep,arr);
      error_z(cnt,dep);
      arrmap[arr] = 1;
    }
    viacnt = 0;
    for (darr = 0; darr < depcnt; darr++) {
      arr = deplst[daofs + darr] & Nbrmask;
      parr = ports + arr;
      if (pdep->tripend && parr->tripstart) deplst[daofs + darr] = arr | Trip0bit;
      vaofs = parr->depofs[2];
      arrcnt = parr->depcnt[2];
      for (dvia = 0; dvia < arrcnt; dvia++) {
        via = deplst[vaofs + dvia] & Nbrmask;
        error_ge(via,portcnt);
        if (arrmap[via] == 0) break;
      }
      if (dvia == arrcnt) continue; // can not be a via
      deplst[daofs + darr] |= Viabit;
      viacnt++;
    }
    pdep->viacnt[2] = viacnt;
    cumviacnt += viacnt;
  }
  info(0,"\ah%u vias",cumviacnt);
  if (cumviacnt == 0) return error0(0,"no vias");

  ofs = 0;
  for (arr = 0; arr < portcnt; arr++) {
    if (progress0(&eta,"arr conn port %u of %u",arr,portcnt)) return 1;
    parr = ports + arr;
    if (parr->valid == 0) continue;
    if (ofs >= pairs) {
      warn(0,"skip port %u on ofs %lu above pairs",arr,ofs);
      continue;
    }
    parr->arrofs[nstop] = (ub4)ofs;
    arrcnt = 0;
    for (dep = 0; dep < portcnt; dep++) {
      if (dep == arr) continue;
      pdep = ports + dep;
      if (pdep->valid == 0) continue;
      cnt = rdiadr2(cnts,dep,arr);
      if (cnt == 0) continue;
      midur = rdiadr2(durlims,dep,arr);
      dasort[arrcnt] = (ub8)midur << 32 | dep;
      arrcnt++;
    }
    parr->arrcnt[nstop] = arrcnt;
    if (arrcnt > 1) fsort8(dasort,arrcnt,0,FLN,"net 1 arrlst");
    else if (arrcnt == 0) continue;
    error_gt(ofs + arrcnt,pairs,arrcnt);
    for (ddep = 0; ddep < arrcnt; ddep++) {
      dep = dasort[ddep] & hi32;
      midur = (ub4)(dasort[ddep] >> 32);
      error_ge(dep,portcnt);
      arrlst[ofs+ddep] = dep;
      arrdurlst[ofs+ddep] = midur;
    }
    ofs += arrcnt;
    error_ovf(ofs,ub4);
  }

  // prepare arr via list
  cumviacnt = 0;
  for (arr = 0; arr < portcnt; arr++) {
    if (progress0(&eta,"arr via port %u of %u",arr,portcnt)) return 1;
    parr = ports + arr;
    if (parr->valid == 0) continue;
    daofs = parr->arrofs[2];
    arrcnt = parr->arrcnt[2];
    nclear(arrmap,portcnt);
    arrmap[arr] = 1;
    for (ddep = 0; ddep < arrcnt; ddep++) {
      dep = arrlst[daofs + ddep] & Nbrmask;
      arrmap[dep] = 1;
    }
    viacnt = 0;
    for (ddep = 0; ddep < arrcnt; ddep++) {
      dep = arrlst[daofs + ddep] & Nbrmask;
      pdep = ports + dep;
      if (pdep->tripend && parr->tripstart) arrlst[daofs + ddep] = dep | Trip0bit;
      vaofs = pdep->arrofs[2];
      depcnt = pdep->arrcnt[2];
      for (dvia = 0; dvia < depcnt; dvia++) {
        via = arrlst[vaofs + dvia] & Nbrmask;
        error_ge(via,portcnt);
        if (arrmap[via] == 0) break;
      }
      if (dvia == depcnt) continue; // can not be a via
      arrlst[daofs + ddep] |= Viabit;
      viacnt++;
    }
    parr->viacnt[2] = viacnt;
    cumviacnt += viacnt;
  }
  info(0,"\ah%u arr vias",cumviacnt);
  afree0(arrmap);

  if (cumviacnt == 0) return error0(0,"no vias");

  net->deplst[nstop] = deplst;
  net->arrlst[nstop] = arrlst;
  net->depdurlst[nstop] = depdurlst;
  net->arrdurlst[nstop] = arrdurlst;

  rmiadr(durlims);

  return 0;
} // end mknet2
