// net1.c - precompute 1-stop connections

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2017 Joris van der Geer.
 */

/*
  Build connectivity matrix between any 2 full ports

  for each dep
    for each via = direct arr of dep
      for each direct arr of via
        store via+typical endtoend time

 Initialize the network once at startup :

   create a pre-computed 1-stop connectivity network used in search

     derived matrix for each of n intermediate hops

     each matrix contains a list of possible trips from port A to port B
     the list is limited to a top-n on average trip duration, and trimmed on heuristics such as distance, cost, timing

     base matrix for direct (non-stop) hops is prepared in net.c
 */

#include <string.h>
#include <pthread.h>

#include "base.h"
#include "cfg.h"
#include "mem.h"
#include "math.h"

static ub4 msgfile;
#include "msg.h"

#include "iadr.h"
#include "util.h"
#include "time.h"
#include "net.h"
#include "net1.h"
#include "netev.h"

#undef hdrstop

static int vrbena;

void ininet1(void)
{
  msgfile = setmsgfile(__FILE__);
  iniassert();
  vrbena = (getmsglvl() >= Vrb);
}

// max number of alternatives per dep,arr pair to consider
#define Durcnt 256

static const ub4 no_airsep = 1; // pending change to un/reserved

// heuristic limit for over-route net1 versus direct
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

static ub4 getvarlim(struct port *pdep,struct port *parr)
{
  ub4 nda = max(pdep->nda,parr->nda);

  if (nda < globs.net1con[0]) return 0;
  else if (nda < globs.net1con[1]) return globs.net1limit[0];
  else if (nda < globs.net1con[2]) return globs.net1limit[1];
  else return globs.net1limit[2];
}

#if 0
// check whether hop2 is to be filtered, given hop1 and net0
static int net1filter(lnet *net,ub4 n0,ub4 *lst0,ub4 hop1,ub4 hop2)
{
  struct chop *hp0,*hp1,*hp2,*hops = net->chops;
  ub4 chopcnt = net->chopcnt;
  ub4 nev0;
  ub4 hop0,v0;

  ub1 *covhrp0,*covhrp1,*covhr = net->covhr;
  ub8 rnghr = net->rnghr;
  ub8 mapofs0,mapofs1;
  ub4 cov0,cov1,h;

  if (hop1 >= chopcnt && hop2 >= chopcnt) return warn(0,"unexpected walk link for %u-%u",hop1,hop2);

  hp1 = hops + hop1;
  hp2 = hops + hop2;
  ub4 lodur1 = hp1->lodur;
  ub4 lodur2 = hp2->lodur;
  ub4 lodur12 = lodur1 + lodur2;

  if (hop2 >= chopcnt) {

    for (v0 = 0; v0 < n0; v0++) {
      hop0 = lst0[v0];
      if (hop0 >= chopcnt) continue;
      hp0 = hops + hop0;

      nev0 = hp0->evcnt;

      if (nev0 == 0) continue;

      mapofs1 = hp1->mapofshr;
      mapofs0 = hp0->mapofshr;
      covhrp1 = covhr + mapofs1;
      covhrp0 = covhr + mapofs0;
      cov1 = cov0 = 0;
      for (h = 0; h < rnghr; h++) {
        if (covhrp1[h] == covhrp0[h]) continue;
        else if (covhrp1[h] > covhrp0[h]) cov1++;
        else cov0++;
      }
      if (hp1->rid == hp0->rid && cov1 == 0) break;
      else if (cov1 == 0 && lodur12 > hp0->hidur && lodur12 - hp0->hidur >= 60 / max(hp0->avgperhr,1)) break;
    }
    if (v0 != n0) return 1;
    else return 0;
  }

  if (hop1 < chopcnt) {

    for (v0 = 0; v0 < n0; v0++) {
      hop0 = lst0[v0];
      if (hop0 >= chopcnt) continue;
      hp0 = hops + hop0;

      nev0 = hp0->evcnt;

      if (nev0 == 0) continue;

      if (hp0->cnthr < min(hp1->cnthr,hp2->cnthr)) continue;
      if (hp0->lodur > lodur12) continue;

      mapofs1 = hp1->mapofshr;
      mapofs0 = hp0->mapofshr;
      covhrp1 = covhr + mapofs1;
      covhrp0 = covhr + mapofs0;
      cov1 = cov0 = 0;
      for (h = 0; h < rnghr; h++) {
        if (covhrp1[h] == covhrp0[h]) continue;
        else if (covhrp1[h] > covhrp0[h]) cov1++;
        else cov0++;
      }
      if (hp1->rid == hp0->rid && cov1 == 0 && hp0->lodur <= lodur12) break;
      else if (cov1 == 0 && lodur12 > hp0->hidur && lodur12 - hp0->hidur >= 60 / max(hp0->avgperhr,1)) break;
    }
    if (v0 != n0) return 1;
    else return 0;
  }

  return 0;
}
#endif

/*
  mid1:12
  v1:10
  v2:10
  dur:16
*/

#define Lst1midbit 12
#define Lst1midcnt (1 << Lst1midbit)
#define Lst1midmask (Lst1midcnt - 1)
#define Lst1vbit 10
#define Lst1vcnt (1 << Lst1vbit)
#define Lst1vmask (Lst1vcnt - 1)
#define Lst1v1shift Lst1midbit
#define Lst1v2shift (Lst1v1shift + Lst1vbit)
#define Lst1durshift (Lst1v2shift + Lst1vbit)
#if Lst1durshift > (64 - 16)
#error "Lst1durshift too large"
#endif
#define Lst1durcnt 65536

// max number of via stops to consider for net1
#define Viacnt1 Lst1midcnt

struct net1_args {
// in
  ub4 tid,tidcnt;
  struct network *net;
  ub4 depfrom,depto;

  ub4 varlimit,var12limit,cntonly;

  ub4 *depmid1s;
  ub4 *depmid1ds;
  ub4 *depmid1cnts;
  ub4 *dmid1cnts;

  ub4 *portdst;

// workspace
  ub4 *aid2s;

// out
  int rv;
  ub8 lstlen;
};

static int net1_pas1(struct net1_args *argp)
{
  ub4 tid = argp->tid;
  ub4 tidcnt = argp->tidcnt;
  ub4 msgtid;

  ub4 *depmid1s = argp->depmid1s;
  ub4 *dmid1ds,*depmid1ds = argp->depmid1ds;
  ub4 *depmid1cnts = argp->depmid1cnts;
  ub4 *dmid1cnts  = argp->dmid1cnts;

  ub4 *dmid1s;
  ub4 *dmid1acnt;
  ub4 dmid1cnt;

  ub4 varlimlh;
  ub4 varlimit = argp->varlimit;
  ub4 var12limit = argp->var12limit;
  ub4 cntonly = argp->cntonly;

  struct network *net = argp->net;

  ub4 portcnt = net->portcnt;
  struct port *pdep,*pmid,*parr,*ports = net->ports;
  iadrbase *cnts0,*precnts;
  ub4 dep,mid,arr;
  ub4 dmid1;
  ub4 cnt,n1,n2,n12;
  ub8 lstlen;
  ub4 cntlim,geocnt;
  ub4 dirdist,dirdistdm,dirdistma,gdistlim;

  ub4 seqdep,seqarr,seqmid;
  ub4 gseqcnt = net->seqdlen;
  ub2 *seqdist = net->seqdist;
  ub1 lotx,*seqlotx = net->seqlotx;
  int havelotx = net->havelotx;

  ub8 stat_var12lim = 0,stat_distlim1 = 0,stat_distlim2 = 0,stat_lotx = 0;

  struct eta eta;

  lstlen = 0;
  ub4 depfrom = argp->depfrom;
  ub4 depto = argp->depto;

  ports = net->ports;

  precnts = &net->conipos;

  cnts0 = net->concnt;

  iadrbase *lstitems = &net->lst1items;

  if (tidcnt > 1) {
    msgtid = (tid << Tidshift) | Tidbit;
    info(msgtid,"start in thread %u",tid);
  } else msgtid = 0;

  info(msgtid,"ports %u-%u of %u",depfrom,depto,portcnt);

  // for each departure port
  for (dep = depfrom; dep < depto; dep++) {

    if (tprogress(tid,tidcnt,&eta,"1-stop pass 1 port %u of %u  \ah%lu conns",dep - depfrom,depto - depfrom,lstlen)) return 2;

    pdep = ports + dep;
    if (pdep->valid == 0) continue;

    dmid1s = depmid1s + dep * Viacnt1;
    dmid1ds = depmid1ds + dep * Viacnt1;
    dmid1acnt = depmid1cnts + dep * Viacnt1;
    dmid1cnt = dmid1cnts[dep];

    if (dmid1cnt == 0) continue;

    seqdep = pdep->gridseq;

    // for each arrival port
    for (arr = 0; arr < portcnt; arr++) {
      if (arr == dep) continue;

      parr = ports + arr;
      if (parr->valid == 0) continue;

      seqarr = parr->gridseq;

      if (havelotx && seqdep != seqarr) {
        lotx = seqlotx[(ub8)seqdep * gseqcnt + seqarr];
        if (lotx > 1) { stat_lotx++; continue; }
      }

      if (cntonly < 256) {
        n1 = rdiadr2(cnts0,dep,arr);
        if (n1 > cntonly) continue;
      }

      varlimlh = getvarlim(pdep,parr);
      error_gt(varlimlh,varlimit,0);
      if (varlimlh == 0) continue;

      dirdist = xgeodist(pdep,parr,seqdep,gseqcnt,seqdist);

      gdistlim = geodistlim(dirdist);

      cnt = cntlim = geocnt = 0;

      error_ovf(lstlen + varlimit * portcnt,ub4);

      // for each via
      for (dmid1 = 0; cnt < varlimlh && dmid1 < dmid1cnt; dmid1++) {

        mid = dmid1s[dmid1];
        if (mid == arr) continue;

        dirdistdm = dmid1ds[dmid1];
        if (dirdistdm > gdistlim) { geocnt = 1; stat_distlim1++; continue; }

        n2 = rdiadr2(cnts0,mid,arr);
        if (n2 == 0) continue;

        pmid = ports + mid;
        seqmid = pmid->gridseq;

        dirdistma = xgeodist(pmid,parr,seqmid,gseqcnt,seqdist);

        if (dirdistdm + dirdistma > gdistlim) {
          geocnt = 1;
          stat_distlim2++;
          continue;
        }

        n2 = min(n2,Lst1vcnt);

        n1 = dmid1acnt[dmid1];
        error_z(n1,dmid1);

        n12 = n1 * n2;
        if (n12 > var12limit) { n12 = var12limit; stat_var12lim++; }
        cnt += n12;
      } // each mid stopover port

      // if (geocnt) cnt++;   // add one tentative item

      cntlim = min(cnt,varlimlh);

      if (cntlim) {
        iadrinc(precnts,dep,arr,tid);
        iadrincn(lstitems,dep,arr * varlimit,cntlim,tid);
        lstlen += cntlim;
      }

    } // each arr

  } // each dep
  argp->lstlen = lstlen;
  info(msgtid,"limits dist \ah%lu \ah%lu  var \ah%lu  lotx \ah%lu",stat_distlim1,stat_distlim2,stat_var12lim,stat_lotx);
  return info(msgtid,"tid %u pass 1 \ah%lu tentative triplets",tid,lstlen);
} // net1 pass 1

static void *net1_pass1(void *vp)
{
  struct net1_args *argp = (struct net1_args *)vp;
  ub4 tid = argp->tid;
  globs.tids[tid] = 1;
  int rv = net1_pas1(argp);
  argp->rv = rv;
  globs.tids[tid] = 0;
  return vp;
}

static int net1_pas2(struct net1_args *argp)
{
  ub4 tid = argp->tid;
  ub4 tidcnt = argp->tidcnt;
  ub4 msgtid;

  ub4 nstop = 1;

  ub4 *dmid1s,*depmid1s = argp->depmid1s;
  ub4 *dmid1ds,*depmid1ds = argp->depmid1ds;
  ub4 *depmid1cnts = argp->depmid1cnts;
  ub4 *dmid1cnts  = argp->dmid1cnts;

  ub4 *dmid1acnt;
  ub4 dmid1cnt;

  ub4 varlimlh;
  ub4 varlimit = argp->varlimit;
  ub4 var12limit = argp->var12limit;
  ub4 cntonly = argp->cntonly;

  ub4 *portdst = argp->portdst;

  struct network *net = argp->net;

  ub4 portcnt = net->portcnt;
  ub4 thopcnt = net->thopcnt;
  ub4 whopcnt = net->whopcnt;
  ub4 aidcnt = net->agencycnt;
  struct port *pdep,*pmid,*parr,*ports = net->ports;
  struct chop *hp1,*hp2,*chops = net->chops;
  block *lstblk0;
  ub4 *portsbyhop;
  iadrbase *cnts0,*precnts,*cnts;
  iadrbase *conofs0;
  ub8 ofs0,ofs1,ofs2;
  ub4 *conlst1,*lst0,*lst1,*lst2;
  ub4 *hopdist = net->hopdist;
  ub1 leg12mode,*hopmode = net->hopmodes;
  ub4 air,aircnt;
  ub4 lodur1,lodur2;
  ub4 dtlo,dthi,typdt,dtcnt;
  ub4 rid1;
  ub4 dep,mid,arr;
  ub4 dmid1;
  ub4 n,n0,n1,n2,n12,altcnt,v1,v2,leg1,leg2;
  ub8 lstlen;
  ub4 dirdist,dirdistdm,dirdistma;
  ub4 dist1,dist2,gdistlim;
  ub4 sumwalkdist1,sumwalkdist2;
  ub4 cntlimdur,gen,outcnt;

  ub4 walklimit = net->net1walklimit;

  ub4 midur,durndx,durcnt,durlim,durcntgnd,durlimgnd;
  ub4 midurs[Durcnt],midursgnd[Durcnt];
  ub4 sortdurs[Durcnt];
  ub4 tmpmodes[Durcnt];
  ub8 tmpitem,tmpitems[Durcnt],tmpitemsgnd[Durcnt];

  ub4 sumwalklimit = net->sumwalklimit;
  ub8 stat_cntlim = 0,stat_partlimdur = 0;
  ub8 stat_var12limit = 0,stat_flt = 0,stat_lotx = 0,stat_varlim = 0;
  ub8 stat_noestdur = 0,stat_estdur = 0,stat_timlim = 0;
  ub4 hicnt = 0;
  ub8 nogen = 0,sumoutcnt = 0;
  ub4 hialt = 0,altdep = 0,altarr = 0;

  struct eta eta;

  lstlen = 0;
  ub4 depfrom = argp->depfrom;
  ub4 depto = argp->depto;
  ub8 tport2 = depto - depfrom;
  tport2 *= tport2;

  ub4 *aid2s = argp->aid2s;
  nclear(aid2s,aidcnt * aidcnt);

  ub4 da_timlim = globs.net1timlim;

  ports = net->ports;

  portsbyhop = net->portsbyhop;

  precnts = &net->conipos;
  conofs0 = net->conofs;

  cnts0 = net->concnt;
  cnts = net->concnt + nstop;

  lstblk0 = net->conlst;
  lst0 = conlst1 = blkdata(lstblk0,0,ub4);

  iadrbase *lstitems = &net->lst1items;
  ub4 hindx,hidur;

  ub4 seqdep,seqmid,seqarr;
  ub4 gseqcnt = net->seqdlen;
  ub2 *seqdist = net->seqdist;
  ub1 lotx,*seqlotx = net->seqlotx;
  int havelotx = net->havelotx;

  if (tidcnt > 1) {
    msgtid = (tid << Tidshift) | Tidbit;
    info(msgtid,"start in thread %u",tid);
  } else msgtid = 0;

  for (dep = depfrom; dep < depto; dep++) {

    pdep = ports + dep;
    if (tprogress(tid,tidcnt,&eta,"p2 port %4u/%u  \ah%lu con %*s",
      dep - depfrom,depto - depfrom,lstlen,*pdep->prefix ? 17 : 0,pdep->prefix)) return 2;

    if (pdep->valid == 0) continue;

    dmid1s = depmid1s + dep * Viacnt1;
    dmid1ds = depmid1ds + dep * Viacnt1;
    dmid1acnt = depmid1cnts + dep * Viacnt1;
    dmid1cnt = dmid1cnts[dep];

    if (dmid1cnt == 0) continue;

    error_ovf(lstlen + 2 * portcnt,ub4);

    if (hi32 - varlimit <= lstlen) {
      warn(msgtid,"limiting net1 to \ah%lu at dep %u of %u",lstlen,dep,portcnt);
      break;
    }

    seqdep = pdep->gridseq;
    outcnt = 0;

    // for each arrival port
    for (arr = 0; arr < portcnt; arr++) {
      if (arr == dep) continue;

      parr = ports + arr;
      if (parr->valid == 0) continue;

      seqarr = parr->gridseq;

      if (havelotx && seqdep != seqarr) {
        lotx = seqlotx[(ub8)seqdep * gseqcnt + seqarr];
        if (lotx > 1) { stat_lotx++; continue; }
      }

      n0 = rdiadr2(cnts0,dep,arr);
      if (cntonly < 256 && n0 > cntonly) continue;

      if (n0) {
        ofs0 = rdiadr8(conofs0,dep,arr);
        lst0 = conlst1 + ofs0;
      }

      if (hi32 - varlimit <= lstlen) {
        warn(msgtid,"limiting net1 to \ah%lu at dep %u of %u arr %u",lstlen,dep,portcnt,arr);
        break;
      }

      setthtimer(tid,da_timlim);

      varlimlh = getvarlim(pdep,parr);
      if (varlimlh == 0) { stat_varlim++; continue; }

      dirdist = xgeodist(pdep,parr,seqdep,gseqcnt,seqdist);

      gdistlim = geodistlim(dirdist);

      gen = 0;

      // todo: start with limits derived from previous nstop
      // e.g. lodists[da] * 2

      // initial heuristic distance-based limit
      if (dirdist < 10) durlim = 60;
      else if (dirdist < 1 * 100) durlim = 2 * 60;
      else if (dirdist < 10 * 100) durlim = 12 * 60;
      else if (dirdist < 100 * 100) durlim = 1 * 1440;
      else if (dirdist < 1000 * 100) durlim = 4 * 1440;
      else if (dirdist < 10000 * 100) durlim = 8 * 1440;
      else durlim = 14 * 1440;
      durlimgnd = durlim;

      cntlimdur = min(varlimlh,Durcnt-1);

      nsethi(midurs,cntlimdur);
      nsethi(midursgnd,cntlimdur);

      // create time top-n list, derive threshold
      altcnt = 0;
      durcnt = 0;
      durcntgnd = 0;

      // for each via
      for (dmid1 = 0; dmid1 < dmid1cnt; dmid1++) {
        dirdistdm = dmid1ds[dmid1];
        if (dirdistdm > gdistlim) continue;
        mid = dmid1s[dmid1];
        if (mid == arr) continue;

        n1 = dmid1acnt[dmid1];
        error_z(n1,dmid1);

        if (isexpired(tid)) { stat_timlim++; break; }

        n2 = rdiadr2(cnts0,mid,arr);
        if (n2 == 0) continue;
        n2 = min(n2,Lst1vcnt);

        pmid = ports + mid;
        seqmid = pmid->gridseq;

        dirdistma = xgeodist(pmid,parr,seqmid,gseqcnt,seqdist);

        if (dirdistdm + dirdistma > gdistlim) continue;

        n12 = 0;

        ofs1 = rdiadr8(conofs0,dep,mid);
        ofs2 = rdiadr8(conofs0,mid,arr);

        error_eq(ofs1,hi32);
        error_eq(ofs2,hi32);

        lst1 = conlst1 + ofs1;
        lst2 = conlst1 + ofs2;

        bound(lstblk0,ofs1,ub4);
        bound(lstblk0,ofs2,ub4);

        // each dep-via-arr alternative
        for (v1 = 0; v1 < n1 && n12 < var12limit; v1++) {
          leg1 = lst1[v1];
          if (leg1 == hi32) {
            error(msgtid,"invalid trip %u-%u-%u",dep,mid,arr);
            break;
          }
          error_ge(leg1,whopcnt);
          hp1 = chops + leg1;

          if (hp1->dep != dep) {
            warn(msgtid,"hop %u %u-%u vs %u-%u",leg1,hp1->dep,hp1->arr,dep,mid);
            continue;
          }

          dist1 = hopdist[leg1];
          if (dist1 > gdistlim) continue;

          if (leg1 >= thopcnt) {
            if (dist1 > walklimit) continue;
            sumwalkdist1 = dist1;
          } sumwalkdist1 = 0;

          air = (hopmode[leg1] & Airbit) | no_airsep;
          lodur1 = hp1->lodur;
          if (lodur1 > (air ? durlim : durlimgnd)) continue;

          rid1 = hp1->rid;

          for (v2 = 0; v2 < n2 && n12 < var12limit; v2++) {
            n12++;

            leg2 = lst2[v2];
            error_ge(leg2,whopcnt);

            dist2 = dist1 + hopdist[leg2];
            if (dist2 > gdistlim) continue;

            hp2 = chops + leg2;
            if (rid1 == hp2->rid && hp2->tripstart == 0) continue;

            sumwalkdist2 = sumwalkdist1;

            if (leg2 >= thopcnt) {
              if (dist2 > walklimit) continue;
              if (leg1 >= thopcnt) continue; // if dep-arr within walkdist, do not add dep-mid-arr
              sumwalkdist2 += hopdist[leg2];
            }

            if (sumwalkdist2 > sumwalklimit) continue;

            // if (n0 && net1filter(net,n0,lst0,leg1,leg2)) { stat_flt++; continue; }

            leg12mode = hopmode[leg1] | hopmode[leg2];
            air = (leg12mode & Airbit) | no_airsep;

            lodur2 = chops[leg2].lodur;

            if (lodur1 + lodur2 > (air ? durlim : durlimgnd)) continue;

            // maintain top-n list
            dtcnt = estdur_2(net,leg1,leg2,&dtlo,&dthi,&typdt);
            midur = typdt;

            if (midur == 0) {
              warn(msgtid,"port %u-%u var %u dur 0 dist %u %s to %s",dep,arr,v1,fgeodist(pdep,parr,1),pdep->iname,parr->iname);
              continue;
            }

            if (dtcnt == 0) {
              stat_noestdur++;
              aid2s[hp1->aid * aidcnt + hp2->aid]++;
              if (stat_noestdur < 10) {
                if (net->agencycnt > 1) warn(0,"no estdur for %u-%u aid %u-%u %s - %s - %s",leg1,leg2,hp1->aid,hp2->aid,pdep->iname,pmid->iname,parr->iname);
                else warn(0,"no estdur for %u-%u %s - %s - %s",leg1,leg2,pdep->iname,pmid->iname,parr->iname);
                estdur_2(net,leg1,leg2,&dtlo,&dthi,&typdt);
              }
              continue;
            } else if (midur > Lst1durcnt) {
              warn(msgtid,"durlim %u exceeds %u",midur,Lst1durcnt);
              continue;
            } else if (midur < lodur1 + lodur2) {
              estdur_2(net,leg1,leg2,&dtlo,&dthi,&typdt);
              midur = typdt;
              error(msgtid|Exit,"hop %u-%u dur %u below min %u+%u",leg1,leg2,midur,lodur1,lodur2);
              continue;
            }
            altcnt++;
            stat_estdur++;
            if (no_airsep && midur > durlim) continue;
            else if (midur > (air ? durlim : durlimgnd)) continue;

            error_gt(durcnt,varlimit,arr);
            error_gt(durcntgnd,varlimit,arr);

            tmpitem = (ub8)dmid1 | ((ub8)v1 << Lst1v1shift) | ((ub8)v2 << Lst1v2shift) | ((ub8)midur << Lst1durshift);

            todo: top-n for lo,mid,hi ?

            // store in both mixed mode and ground-only. select part of each if needed lateron
            if (durcnt == 0) { // first item
              midurs[0] = midur;
              tmpitems[0] = tmpitem;
              tmpmodes[0] = leg12mode;
              warncc(midur != hi32 && midur > 65534,Exit|msgtid,"durlim %u at 0 of %u exceeds 64k",midur,cntlimdur);
              durcnt = 1;
            } else if (durcnt < cntlimdur) { // next items
              warncc(midur != hi32 && midur > 65534,Exit|msgtid,"durlim %u at %u of %u exceeds 64k",midur,durcnt,cntlimdur);
              tmpitems[durcnt] = tmpitem;
              tmpmodes[durcnt] = leg12mode;
              midurs[durcnt++] = midur;
            } else { // full: eventually replace slower entry
              hidur = hindx = 0;
              for (durndx = 0; durndx < cntlimdur; durndx++) {
                if (midurs[durndx] > hidur) { hidur = midurs[durndx]; hindx = durndx; }
                warncc(midurs[durndx] != hi32 && midurs[durndx] > 65534,Exit|msgtid,"durlim %u at %u of %u exceeds 64k",midurs[durndx],durndx,cntlimdur);
              }
              durlim = hidur;
              warncc(durlim != hi32 && durlim > 65534,Exit|msgtid,"durlim %u at %u exceeds 64k",durlim,cntlimdur);
              error_eq(durlim,hi32);
              if (midur < hidur) {
                midurs[hindx] = midur;
                tmpitems[hindx] = tmpitem;
                tmpmodes[hindx] = leg12mode;
              }
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

          } // each v2
        } // each v1

        if (n12 == var12limit) stat_var12limit++;
      } // each mid
      if (altcnt > hialt) { hialt = altcnt; altdep = dep; altarr = arr; }

      error_gt(durcnt,varlimlh,dep);

      if (durcnt == cntlimdur) stat_partlimdur++;
      warncc(durlim != hi32 && durlim > 65534,Exit|msgtid,"durlim %u exceeds 64k",durlim);

      if (durcnt == 0) { nogen++; continue; }

      // emit mixed tmpitems only, or best half of tmpitems and -gnd if needed
      iadrinc(cnts,dep,arr,tid);
      outcnt++;

      aircnt = 0;
      for (n = 0; n < durcnt; n++) {
        if (tmpmodes[n] & Airbit) aircnt++;
      }

      if (no_airsep || aircnt * 2 <= cntlimdur) { // mixed only

        error_gt(durcnt,varlimlh,dep);
        error_gt(durcnt,cntlimdur,dep);

        for (n = 0; n < durcnt; n++) {
          tmpitem = tmpitems[n];
          if (wriadr8(lstitems,dep,arr * varlimit + n,tmpitem)) {
            info(0,"dep %u arr %u n %u varlim %u dist %u",dep,arr,n,varlimit,dirdist);
            break;
          }
        }
        if (n < durcnt) continue;
        if (wriadr2(precnts,dep,arr,(ub2)n)) {
          info(0,"dep %u arr %u n %u varlim %u dist %u",dep,arr,n,varlimit,dirdist);
          continue;
        }
        lstlen += n;
        continue;
      }

      // best half of each
      for (n = 0; n < durcnt; n++) sortdurs[n] = (midurs[n] << 16) | n;
      sort4(sortdurs,durcnt,FLN,"net1 midurs");
      n = gen = 0;
      while (n < durcnt && gen < cntlimdur / 2) {
        hindx = sortdurs[gen] & hi16;
        error_ge(hindx,durcnt);
        tmpitem = tmpitems[hindx];
        if (wriadr8(lstitems,dep,arr * varlimit + gen,tmpitem)) { n = 0; break; }
        gen++;
      }
      if (n == 0) continue;
      lstlen += gen;

      if (durcntgnd == 0) {
        if (wriadr2(precnts,dep,arr,(ub2)gen)) info(0,"dep %u arr %u n %u varlim %u dist %u",dep,arr,n,varlimit,dirdist);
        continue;
      }

      for (n = 0; n < durcntgnd; n++) sortdurs[n] = (midursgnd[n] << 16) | n;
      sort4(sortdurs,durcntgnd,FLN,"net1 midurs");

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

      if (wriadr2(precnts,dep,arr,(ub2)gen)) {
        info(0,"dep %u arr %u n %u varlim %u dist %u",dep,arr,n,varlimit,dirdist);
        continue;
      }
      lstlen += gen;

    } // each arrival port
    portdst[dep] = outcnt;
    sumoutcnt += outcnt;

  } // each departure port

  setthtimer(tid,0);

  ub4 aid2,hiaidcnt = 0,hiaid2 = 0;
  for (aid2 = 0; aid2 < aidcnt * aidcnt; aid2++) {
    if (aid2s[aid2] > hiaidcnt) { hiaidcnt = aid2s[aid2]; hiaid2 = aid2; }
  }

  ub8 allestdur = stat_estdur + stat_noestdur;
  info(msgtid|CC0,"no estdur \ah%lu of \ah%lu = \ap%lu%lu  \ah%u at hi aid %u-%u",
    stat_noestdur,allestdur,stat_noestdur,allestdur,hiaidcnt,hiaid2 / aidcnt,hiaid2 % aidcnt);

  estdur2_stats(tid);

  info(msgtid,"limits hicnt \ah%u cntlim \ah%lu partlim dur \ah%lu time \ah%lu var12 \ah%lu",hicnt,stat_cntlim,stat_partlimdur,stat_timlim,stat_var12limit);
  info(msgtid,"  var \ah%lu lotx \ah%lu",stat_varlim,stat_lotx);

  info(msgtid,"%u-stop p2: \ah%lu triplets in \ah%lu pairs, \ap%lu%lu",nstop,lstlen,sumoutcnt,sumoutcnt,tport2);
  info(msgtid,"  \ah%lu filtered \ah%lu nogen",stat_flt,nogen);

  pdep = ports + altdep;
  parr = ports + altarr;
  msgopt("pass1"); info(msgtid,"high alt %u for %u-%u %s %s",hialt,altdep,altarr,pdep->iname,parr->iname);

  argp->lstlen = lstlen;

  return 0;
}

static void *net1_pass2(void *vp)
{
  struct net1_args *argp = (struct net1_args *)vp;
  ub4 tid = argp->tid;
  globs.tids[tid] = 1;
  int rv = net1_pas2(argp);
  argp->rv = rv;
  globs.tids[tid] = 0;
  rmthtimer(tid);
  return vp;
}

// create 1-stop connectivity matrix and derived info
// uses 1 via from 0-stop net
int mknet1(struct network *net,ub4 varlimit,ub4 var12limit,ub4 cntonly,ub4 netstop)
{
  ub4 nstop = 1;
  ub4 portcnt = net->portcnt;
  ub4 hopcnt = net->hopcnt;
  ub4 thopcnt = net->thopcnt;
  ub4 whopcnt = net->whopcnt;
  struct port *ports,*pmid,*pdep,*parr;
  block *lstblk,*lstblk0;
  ub4 *portsbyhop;
  iadrbase *cnts,*cnts0,*precnts;
  iadrbase *conofs,*conofs0;
  ub4 *portdst;
  ub8 ofs,ofs1,ofs2,endofs,lstlen,tlstlen,newlstlen;
  ub4 *lst,*newlst,*conlst1,*lst1,*lst2,*lstv1;
  ub4 *hopdist = net->hopdist;
  ub4 dep,mid,arr,dep2;
  ub4 dmid1;
  ub4 iv;
  ub4 cnt,n,n1,n2,v1,v2,leg,leg1,leg2,nleg;
  ub4 dist1,dist2,sumwalkdist2,walkdist1,walkdist2,maxwalk;
  ub4 gen;
  ub4 midur,durlim;
  ub8 lstitem;
  ub4 stat_nocon = 0,stat_partcnt = 0,stat_cntlim = 0,stat_partlimdur = 0;

  struct eta eta;

  if (varlimit == 0) return warn0(0,"skip 1-stop net on zero limit");

  error_zz(portcnt,hopcnt);

  info(0,"init %u-stop connections for %u port \ah%u hop network",nstop,portcnt,whopcnt);

  info(0,"limits: var %u var12 %u",varlimit,var12limit);

  ports = net->ports;

  portsbyhop = net->portsbyhop;

  precnts = &net->conipos;
  clear(precnts);
  cnts = net->concnt + nstop;
  conofs = net->conofs + nstop;

  ub4 sparsethres = net->sparsethres;

  iadrbase *lstitems = &net->lst1items;
  iadrbase *durlims = net->durlims + nstop;

  error_lt(varlimit,globs.net1limit[0]);
  error_lt(varlimit,globs.net1limit[1]);
  error_ne(varlimit,globs.net1limit[2]);

  if (mkiadr0(lstitems,portcnt,portcnt * varlimit,ub8,sparsethres,32,"net1 lstitems")) return 1;
  if (setiadropts(lstitems,Iadr_append | Iadr_softlim)) return 1;

  // main net1 structure
  if (mkiadr0(precnts,portcnt,portcnt,ub2,sparsethres,10,"net1 precnts")) return 1;
  if (setiadropts(precnts,Iadr_softlim)) return 1;

  if (mkiadr0(cnts,portcnt,portcnt,ub2,sparsethres,10,"net1 cnts")) return 1;
  if (mkiadr0(conofs,portcnt,portcnt,ub8,sparsethres,10,"net1 ofs")) return 1;

  if (mkiadr0(durlims,portcnt,portcnt,ub2,sparsethres,10,"net1 durlims")) return 1;
  setiadropts(durlims,Iadr_defhi);

  portdst = talloc(portcnt, ub4,0,"net portdst",portcnt);  // outbound conn stats

  error_zp(hopdist,0);

  nleg = nstop + 1;

/* Essentially we do for each (departure,arrival) pair:
   Search for a 'via' port such that trip (dep,via) and (via2,arr) exist
   Trim list of alternatives based on typical trip duration
   Store result by value. This is memory-intensive but keeps code simple

   In short:
   foreach dep
     foreach arr
       foreach mid with [dep,mid]
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

  // prepare mid lookup info
  ub4 *dmid1s,*depmid1s = talloc(portcnt * Viacnt1,ub4,0,"net depdmid",Viacnt1);
  ub4 dir,*dmid1ds,*depmid1ds = talloc(portcnt * Viacnt1,ub4,0,"net depdmidd",Viacnt1);
  ub4 *dmid1acnt,*depmid1cnts = talloc(portcnt * Viacnt1,ub4,0,"net depdmid",Viacnt1);

  ub4 *dmid1cnts = talloc(portcnt,ub4,0,"net depdmidcnt",portcnt);

  cnts0 = net->concnt;

  lstblk0 = net->conlst;
  conlst1 = blkdata(lstblk0,0,ub4);
  conofs0 = net->conofs;

  ub4 fltdepcnt = 0;
  ub4 dmidbins[Viacnt1];
  ub4 dmidivs = Elemcnt(dmidbins) - 1;;
  aclear(dmidbins);
  ub4 dmid,ddep,*deplst0 = net->deplst[0];
  ub4 depofs,depcnt;

  // prepare vias
  for (dep = 0; dep < portcnt; dep++) {

    if (progress0(&eta,"1-stop pass 0 dep %u of %u",dep,portcnt)) return 1;

    pdep = ports + dep;
    if (pdep->valid == 0) continue;

    depofs = pdep->depofs[0];
    depcnt = pdep->depcnt[0];

    dmid1s = depmid1s + dep * Viacnt1;
    dmid1ds = depmid1ds + dep * Viacnt1;
    dmid1acnt = depmid1cnts + dep * Viacnt1;
    dmid1 = 0;
    for (dmid = 0; dmid < depcnt && dmid1 < Viacnt1; dmid++) {
      ddep = deplst0[depofs + dmid];
      mid = ddep & Nbrmask;
      if ( (ddep & Viabit) == 0 && (ddep & Tripbits) != Tripbits ) continue;
      pmid = ports + mid;

      n1 = rdiadr2(cnts0,dep,mid);
      errorcc(n1 == 0,0,"dep %u mid #%u = %u no conns",dep,dmid,mid);

      n1 = min(n1,Lst1vcnt);
      dmid1acnt[dmid1] = n1;

      dir = fgeodist(pdep,pmid,1);
      dmid1ds[dmid1] = dir;
      dmid1s[dmid1++] = mid;
    }
    // info(0,"port %u: %u",dep,dmid1);
    dmid1cnts[dep] = dmid1;
    dmidbins[min(dmid1,dmidivs)]++;
    if (dmid1 == Viacnt1) {
      fltdepcnt++;
      info(Iter,"dep %u limiting mid to %u %s",dep,dmid1,pdep->iname);
    }
  }
  for (iv = 0; iv <= dmidivs; iv++) { dmid1 = dmidbins[iv]; infocc(dmid1,Notty,"dmids %u: \ah%u",iv,dmid1); }
  info(CC0,"%u dep limited on %u vias",fltdepcnt,Viacnt1);

  // see net2 for comment
  ub4 depfrom,depto,depchunk;
  int rv;
  void *trv;

  ub4 aidcnt = net->agencycnt;
  ub4 aid2 = aidcnt * aidcnt;
  struct net1_args *argp,*argp0,*argp1,*targs = talloc(Nthread+1,struct net1_args,0,"net1 tidargs",0);
  pthread_t ptids[Nthread];

  argp0 = targs;
  argp1 = targs + Nthread;  // for last partial;

  ub4 tid = 0;
  ub4 tidcnt = portcnt > 5000 ? globs.tidcnt : 1;

  argp0->tid = 0;
  argp0->tidcnt = tidcnt;
  argp0->net = net;
  argp0->depfrom = 0;
  argp0->depto = portcnt;

  argp0->varlimit = varlimit;
  argp0->var12limit = var12limit;
  argp0->cntonly = cntonly;

  argp0->portdst = portdst;

  argp0->depmid1s = depmid1s;
  argp0->depmid1ds = depmid1ds;
  argp0->depmid1cnts = depmid1cnts;
  argp0->dmid1cnts = dmid1cnts;

  argp0->aid2s = talloc(aid2,ub4,0,"net aid",aidcnt);

  if (tidcnt == 1) {
    rv = net1_pas1(argp0);
    if (rv) return rv;
    tlstlen = targs->lstlen;
  } else {
    depchunk = (portcnt / tidcnt) & (~Maxmask);
    info(0,"%u threads, %u ports in chunks of %u",tidcnt,portcnt,depchunk);

    argp0->depto = min(depchunk,portcnt);
    depfrom = depchunk;
    for (tid = 1; tid < tidcnt && depfrom < portcnt - 1; tid++) {
      argp = targs + tid;
      *argp = *argp0;
      argp->tid = tid;
      argp->aid2s = talloc(aid2,ub4,0,"net aid",aidcnt);
      argp->depfrom = depfrom;
      argp->depto = depto = min(depfrom + depchunk,portcnt);
      pdep = ports + depfrom;
      parr = ports + depto;
      info(0,"tid %u %u-%u %s %s",tid,depfrom,depto,pdep->iname,parr->iname);
      depfrom += depchunk;
    }

    if (depfrom < portcnt - 1) {  // last partial chunk
      *argp1 = *argp0;
      argp1->aid2s = talloc(aid2,ub4,0,"net aid",aidcnt);
      argp1->depfrom = depfrom;
      argp1->depto = portcnt;
      if (net1_pas1(argp1)) return error(0,"net1 pass 1 partial chunk %u-%u failed",depfrom,portcnt);
    }

    for (tid = 1; tid < tidcnt; tid++) {
      argp = targs + tid;
      if (argp->depto == 0) continue;
      rv = pthread_create(ptids + tid,NULL,&net1_pass1,argp);
      if (rv) return oserror(0,"cannot create thread %u",tid);
      info(0,"created thread %u: ports %u-%u",tid,argp->depfrom,argp->depto);
    }

    // first chunk in main thread
    net1_pass1(targs);
    rv = targs->rv;
    if (rv == 2) return 1;
    else if (rv) return error(0,"net1 pass 1 chunk %u-%u failed",0,depchunk);
    tlstlen = targs->lstlen;

    for (tid = 1; tid < tidcnt; tid++) {
      argp = targs + tid;
      if (argp->depto == 0) continue;
      info(0,"joining thread %u",tid);
      if (pthread_join(ptids[tid],&trv)) return oserror(0,"cannot join thread %u",tid);
      if (trv == NULL) return error(0,"thread %u returned nil error",tid);
      argp = (struct net1_args *)trv;
      rv = argp->rv;
      if (rv) return error(0,"thread %u returned error %d",tid,rv);
      info(0,"joined thread %u",tid);
      tlstlen += argp->lstlen;
    }
    info(Emp,"1-stop pass 1 \ah%lu tentative triplets",tlstlen);
  }
  if (tlstlen == 0) return error0(0,"no triplets");

  // pass 2
  mkiadr1(precnts);
  mkiadr1(lstitems);

  if (tidcnt == 1) {
    rv = net1_pas2(argp0);
    if (rv) return rv;
  } else {
    depchunk = (portcnt / tidcnt) & (~Maxmask);
    info(0,"%u threads, %u ports in chunks of %u",tidcnt,portcnt,depchunk);

    if (argp1->depto) {  // last partial chunk
      if (net1_pas2(argp1)) return error(0,"net1 pass 2 partial chunk %u-%u failed",argp1->depfrom,portcnt);
    }

    for (tid = 1; tid < tidcnt; tid++) {
      argp = targs + tid;
      if (argp->depto == 0) continue;
      info(0,"creating thread %u: ports %u-%u",tid,argp->depfrom,argp->depto);
      rv = pthread_create(ptids + tid,NULL,&net1_pass2,argp);
      if (rv) return oserror(0,"cannot create thread %u",tid);
      info(0,"created thread %u",tid);
    }

    // first chunk in main thread
    net1_pass2(argp0);
    rv = argp0->rv;
    if (rv == 2) return 1;
    else if (rv) return error(0,"net1 pass 2 chunk %u-%u failed",0,depchunk);

    for (tid = 1; tid < tidcnt; tid++) {
      argp = targs + tid;
      if (argp->depto == 0) continue;
      info(0,"joining thread %u",tid);
      if (pthread_join(ptids[tid],&trv)) return oserror(0,"cannot join thread %u",tid);
      if (trv == NULL) return error(0,"thread %u returned nil error",tid);
      argp = (struct net1_args *)trv;
      rv = argp->rv;
      if (rv) return error(0,"thread %u returned error %d",tid,rv);
      info(0,"joined thread %u",tid);
    }
  }
  for (tid = 0; tid < tidcnt; tid++) {
    argp = targs + tid;
    if (argp->aid2s) afree(argp->aid2s,"net");
  }
  if (argp1->aid2s) afree(argp1->aid2s,"net");

  ofs = 0;

  for (dep = 0; dep < portcnt; dep++) {

    if (progress(&eta,"1-stop pass 2b port %u of %u  \ah%lu conns",dep,portcnt,ofs)) return 1;

    for (arr = 0; arr < portcnt; arr++) {
      if (arr == dep) continue;

      gen = rdiadr2(precnts,dep,arr);
      if (gen == 0) continue;

      ofs += gen;
    }
  }
  lstlen = ofs;
  info(Emp,"pass 2 %u stop done, \ah%lu triplets",nstop,lstlen);

  struct range portdr;
  ub4 ivportdst[32];

  mkhist(caller,portdst,portcnt,&portdr,Elemcnt(ivportdst),ivportdst,"outbounds by port",Info);

  warncc(lstlen == 0,0,"no connections at %u-stop for %u ports",nstop,portcnt);
  if (lstlen == 0) return 0;

  mkiadr1(cnts);

  cpiadr(durlims,cnts);
  mkiadr1(durlims);

  cpiadr(conofs,cnts);
  mkiadr1(conofs);

  ub4 cnt0,newcnt;

  ub4 genstats[64];
  ub4 cntstats[64];
  ub4 geniv = 63;

  aclear(cntstats);
  aclear(genstats);

  // prepare list matrix

  lstblk = net->conlst + nstop;

  lst = mkblock(lstblk,(ub8)lstlen * nleg,ub4,Noinit,"net1 %u-stop conlst",nstop);

  ub1 *modes = alloc(lstlen,ub1,0,"net1 modes",lstlen);
  ub1 *hopmode = net->hopmodes;

  ofs = newcnt = 0;

  if (portcnt < 20000) {
    for (dep = 0; dep < portcnt; dep++) {
      for (arr = 0; arr < portcnt; arr++) {
        if (dep == arr) continue;
        cnt = rdiadr2(precnts,dep,arr);
        cnt0 = rdiadr2(cnts0,dep,arr);
        if (cnt) {
          ofs += cnt;
          if (cnt0 == 0) newcnt++;
        }
      }
    }
    info(0,"\ah%u new connections",newcnt);
    error_ne(ofs,lstlen);
  }

  aclear(dupstats);

  ub8 dursort[Durcnt];
  ub4 *tmpv1,tmplst[Durcnt * 2];
  ub1 tmpmodes[Durcnt];
  ub4 idx,idx2;
  ub4 pairs = 0;
  ub4 durwarn = 0;

  // pass 3: fill based on triplets determined above
  ofs = 0;
  for (dep = 0; dep < portcnt; dep++) {

    if (progress(&eta,"1-stop pass 3 port %u of %u  \ah%lu conns",dep,portcnt,ofs)) return 1;

    pdep = ports + dep;

    if (pdep->valid == 0) continue;

    dmid1s = depmid1s + dep * Viacnt1;
    dmid1acnt = depmid1cnts + dep * Viacnt1;

    for (arr = 0; arr < portcnt; arr++) {
      if (arr == dep) continue;

      cnt = rdiadr2(precnts,dep,arr);
      if (cnt == 0) continue;

      cnt = min(cnt,Durcnt);
      if (wriadr2(cnts,dep,arr,(ub2)cnt)) return 1;
      parr = ports + arr;

      error_z(parr->valid,arr);

      gen = 0; // generate final count

      if (wriadr8(conofs,dep,arr,ofs)) return 1;

      lstv1 = lst + ofs * nleg;
      error_ge(ofs,lstlen);
      tmpv1 = tmplst;

      endofs = ofs + cnt - 1;

      error_ge(endofs,lstlen);

      for (n = 0; n < cnt; n++) {
        lstitem = rdiadr8(lstitems,dep,arr * varlimit + n);
        dmid1 = lstitem & Lst1midmask;
        mid = dmid1s[dmid1];

        v1 = (lstitem >> Lst1v1shift) & Lst1vmask;
        v2 = (lstitem >> Lst1v2shift) & Lst1vmask;

        midur = (ub2)(lstitem >> Lst1durshift);

        if (midur == 0) {
          warncc(durwarn++ < 100,0,"port %u-%u var %u dur 0 dist %u %s to %s",dep,arr,n,fgeodist(pdep,parr,1),pdep->iname,parr->iname);
          continue;
        }
        n1 = dmid1acnt[dmid1];
        error_ge(v1,n1);

        ofs1 = rdiadr8(conofs0,dep,mid);
        lst1 = conlst1 + ofs1;

        n2 = rdiadr2(cnts0,mid,arr);
        error_z(n2,mid);
        error_ge(v2,n2);

        ofs2 = rdiadr8(conofs0,mid,arr);

        lst2 = conlst1 + ofs2;

        bound(lstblk0,ofs1,ub4);
        bound(lstblk0,ofs2,ub4);

        leg1 = lst1[v1];
        error_ge(leg1,whopcnt);

        if (portsbyhop[leg1 * 2] != dep) {
          error(Exit,"hop %u %u-%u vs %u-%u",leg1,portsbyhop[leg1 * 2],portsbyhop[leg1 * 2 + 1],dep,mid);
        }
        error_ne(portsbyhop[leg1 * 2],dep);

        if (portsbyhop[leg1 * 2 + 1] != mid) {
          info(0,"dmid1 %u mid1 %u n %u of %u",dmid1,mid,v1,n1);
          error(Exit,"arr %u hop %u %u-%u vs %u-%u",arr,leg1,portsbyhop[leg1 * 2],portsbyhop[leg1 * 2 + 1],dep,mid);
        }
        error_ne(portsbyhop[leg1 * 2 + 1],mid);

        leg2 = lst2[v2];
        error_ge(leg2,whopcnt);
        dep2 = portsbyhop[leg2 * 2];

        if (dep2 != mid) {
          error(Exit,"hop %u %u-%u vs %u-%u",leg2,dep2,portsbyhop[leg2 * 2 + 1],mid,arr);
        }
        error_ne(dep2,mid);
        error_ne(portsbyhop[leg2 * 2 + 1],arr);

        dist1 = hopdist[leg1];
        if (leg1 >= thopcnt) walkdist1 = dist1; else walkdist1 = 0;

        dist2 = hopdist[leg2];
        if (leg2 >= thopcnt) walkdist2 = dist2; else walkdist2 = 0;

        sumwalkdist2 = walkdist1 + walkdist2;

        maxwalk = max(walkdist2,walkdist1);

        error_ge(gen,Elemcnt(dursort));
        dursort[gen] = (ub8)midur << 32 | gen;

        tmpmodes[gen] = hopmode[leg1] | hopmode[leg2];

        error_ovf(maxwalk,ub2);
        error_ovf(sumwalkdist2,ub2);

        error_gt((ub8)(tmpv1 + 2),(ub8)(tmplst + Elemcnt(tmplst)),gen);

        tmpv1[0] = leg1;
        tmpv1[1] = leg2;

        if (checktrip3(net,tmpv1,nleg,dep,arr,mid,dist1 + dist2)) return 1;
        gen++;

        tmpv1 += nleg;

      } // each alt

      if (gen < cnt) stat_partcnt++;

      genstats[min(gen,geniv)]++;
      cntstats[min(cnt,geniv)]++;

      // none found for any dep-Mid-arr, but mid exists : no events
      if (cnt && gen == 0) stat_nocon++;

      if (gen == 0) continue;

      pairs++;

      error_gt(gen,cnt,arr);

      if (gen > 1) sort8(dursort,gen,FLN,"nstop durlist");
      durlim = (ub4)(dursort[0] >> 32);
      for (idx = 0; idx < gen; idx++) {
        idx2 = dursort[idx] & hi32;
        error_ge(idx2,gen);
        memcpy(lstv1,tmplst + idx2 * nleg,nleg * sizeof(ub4));
        modes[ofs + idx] = tmpmodes[idx2];
        lstv1 += nleg;
      }

     cnt = 2  8+2+2*2*4 = 26   -> 4+2*2*2 = 12
     cnt = 4  8+2+4*2*4 = 42      4+4*2*2 = 20
     cnt = 8  8+2+8*2*4 = 102     4+8*2*2 = 36

        todo store index in deplst instead of hop
        counts and ub4 offset combined

      ofs += gen;
      if (wriadr2(cnts,dep,arr,(ub2)gen)) return 1;
      if (wriadr2(durlims,dep,arr,(ub2)durlim)) return 1; ? // use best as base for net2

    } // each arrival port
  } // each departure port

  afree(depmid1s,"net");
  afree(depmid1ds,"net");
  afree(depmid1cnts,"net");

  newlstlen = (ub4)ofs;
  error_gt(newlstlen,lstlen,0);

  rmiadr(lstitems);
  rmiadr(precnts);

  finiadr(cnts);
  finiadr(conofs);

  ub8 conperc = (100UL * pairs) / ((ub8)portcnt * portcnt);
  info(Emp,"pass 3 net %u done, \ah%lu from \ah%lu triplets in \ah%u pairs %lu%%",nstop,newlstlen,lstlen,pairs,conperc);

  if (lstlen - newlstlen > 1024 * 1024 * 64) {
    newlst = trimblock(lstblk,newlstlen * nleg,ub4);
  } else newlst = lst;

  net->lstlen[nstop] = newlstlen;
  net->pairs[nstop] = pairs;

  info(0,"verify \ah%lu hops",newlstlen);
  for (ofs = 0; ofs < newlstlen * nleg; ofs++) {
    leg = newlst[ofs];
    error_ge(leg,whopcnt);
  }
  for (ofs = 0; ofs < newlstlen; ofs++) {
    error_z(modes[ofs],ofs);
  }

  for (iv = 0; iv < Elemcnt(dupstats); iv++) if (dupstats[iv]) info(0,"dup %u: \ah%lu",iv,dupstats[iv]);

  info(0,"no conn %u  partcnt %u  cntlim %u partlim1 %u",stat_nocon,stat_partcnt,stat_cntlim,stat_partlimdur);

  for (iv = 0; iv <= geniv; iv++) infocc(cntstats[iv],V0,"%u: gen \ah%u cnt \ah%u",iv,genstats[iv],cntstats[iv]);

  net->modes[nstop] = modes;

  // verify all triplets

  for (dep = 0; dep < portcnt && portcnt < 50000; dep++) {
    if (progress0(&eta,"verify trips port %u of %u",dep,portcnt)) return 1;
    pdep = ports + dep;
    for (arr = 0; arr < portcnt; arr++) {
      if (dep == arr) continue;
      n1 = rdiadr2(cnts,dep,arr);
      if (n1 == 0) continue;
      parr = ports + arr;

      ofs = rdiadr8(conofs,dep,arr);
      lstv1 = newlst + ofs * nleg;
      for (v1 = 0; v1 < n1; v1++) {
        if (checktrip(net,lstv1,nleg,dep,arr,hi32)) {
          info(0,"dep %u arr %u n %u",dep,arr,v1);
          break;
        }
        lstv1 += nleg;
      }
    }
  }

  if (dorun(FLN,Runserver,1) == 0) {
    if (netstop == 1) rmiadr(durlims);
    else finiadr(durlims);
    return 0;
  }

  // prepare sorted outbounds and inbounds per port for search
  ub4 arrcnt,viacnt,darr,dvia,via;
  ub4 *deplst = alloc(pairs,ub4,0,"net1 deplst",0);
  ub4 *arrlst = alloc(pairs,ub4,0,"net1 arrlst",0);
  ub4 *depdurlst = alloc(pairs,ub4,0,"net1 deplst",0);
  ub4 *arrdurlst = alloc(pairs,ub4,0,"net1 deplst",0);

  ub8 *dasort = talloc(portcnt,ub8,0,"net0 depsort",0);
  ub4 daofs,vaofs;

  ofs = 0;

  for (dep = 0; dep < portcnt && pairs; dep++) {
    if (progress0(&eta,"dep conlst port %u of %u",dep,portcnt)) return 1;
    pdep = ports + dep;
    if (pdep->valid == 0) continue;
    if (ofs >= pairs) {
      warn(0,"skip dep %u on ofs %lu above \ah%u pairs",dep,ofs,pairs);
      continue;
    }
    pdep->depofs[1] = (ub4)ofs;
    depcnt = 0;
    for (arr = 0; arr < portcnt; arr++) {
      if (dep == arr) continue;
      parr = ports + arr;
      cnt = rdiadr2(cnts,dep,arr);
      if (cnt == 0) continue;
      durlim = rdiadr2(durlims,dep,arr);
      dasort[depcnt] = (ub8)durlim << 32 | arr;
      depcnt++;
    }
    pdep->depcnt[1] = depcnt;

    if (depcnt > 1) sort8(dasort,depcnt,FLN,"net 1 deplst");
    else if (depcnt == 0) continue;
    error_gt(ofs + depcnt,pairs,depcnt);
    for (darr = 0; darr < depcnt; darr++) {
      arr = dasort[darr] & hi32;
      durlim = (ub4)(dasort[darr] >> 32);
      deplst[ofs+darr] = arr;
      depdurlst[ofs+darr] = durlim;
    }
    ofs += depcnt;
  }
  error_ne(ofs,pairs);

  ub4 cumviacnt = 0;
  ub1 *arrmap = talloc0(portcnt,ub1,0);

  // prepare dep via list
  for (dep = 0; dep < portcnt; dep++) {
    if (progress0(&eta,"dep vialst port %u of %u",dep,portcnt)) return 1;
    pdep = ports + dep;
    if (pdep->valid == 0) continue;
    daofs = pdep->depofs[1];
    depcnt = pdep->depcnt[1];
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
      vaofs = parr->depofs[1];
      arrcnt = parr->depcnt[1];
      for (dvia = 0; dvia < arrcnt; dvia++) {
        via = deplst[vaofs + dvia] & Nbrmask;
        error_ge(via,portcnt);
        if (arrmap[via] == 0) break;
      }
      if (dvia == arrcnt) continue; // can not be a via
      deplst[daofs + darr] |= Viabit;
      viacnt++;
    }
    pdep->viacnt[1] = viacnt;
    cumviacnt += viacnt;
  }
  info(0,"\ah%u vias",cumviacnt);
  if (cumviacnt == 0) return error0(0,"no vias");

  ub4 hicnt = 0;
  ofs = 0;
  for (arr = 0; arr < portcnt && pairs; arr++) {
    if (progress0(&eta,"arr conn port %u of %u",arr,portcnt)) return 1;
    parr = ports + arr;
    if (parr->valid == 0) continue;
    if (ofs >= pairs) {
      warn(0,"skip arr %u on ofs %lu above \ah%u pairs",arr,ofs,pairs);
      continue;
    }
    parr->arrofs[1] = (ub4)ofs;
    arrcnt = 0;
    for (dep = 0; dep < portcnt; dep++) {
      if (dep == arr) continue;
      pdep = ports + dep;
      if (pdep->valid == 0) continue;
      cnt = rdiadr2(cnts,dep,arr);
      if (cnt == 0) continue;
      durlim = rdiadr2(durlims,dep,arr);
      dasort[arrcnt] = (ub8)durlim << 32 | dep;
      arrcnt++;
    }
    parr->arrcnt[1] = arrcnt;
    if (arrcnt > 1) sort8(dasort,arrcnt,FLN,"net 1 arrlst");
    else if (arrcnt == 0) continue;
    if (arrcnt > hicnt) hicnt = arrcnt;
    error_gt(ofs + arrcnt,pairs,arrcnt);
    for (ddep = 0; ddep < arrcnt; ddep++) {
      dep = dasort[ddep] & hi32;
      durlim = (ub4)(dasort[ddep] >> 32);
      arrlst[ofs+ddep] = dep;
      arrdurlst[ofs+ddep] = durlim;
    }
    ofs += arrcnt;
  }
  error_ne(ofs,pairs);

  // prepare arr via list
  cumviacnt = 0;
  for (arr = 0; arr < portcnt; arr++) {
    if (progress0(&eta,"arr conn port %u of %u",arr,portcnt)) return 1;
    parr = ports + arr;
    if (parr->valid == 0) continue;
    daofs = parr->arrofs[1];
    arrcnt = parr->arrcnt[1];
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
      vaofs = pdep->arrofs[1];
      depcnt = pdep->arrcnt[1];
      for (dvia = 0; dvia < depcnt; dvia++) {
        via = arrlst[vaofs + dvia] & Nbrmask;
        error_ge(via,portcnt);
        if (arrmap[via] == 0) break;
      }
      if (dvia == depcnt) continue; // can not be a via
      arrlst[daofs + ddep] |= Viabit;
      viacnt++;
    }
    parr->viacnt[1] = viacnt;
    cumviacnt += viacnt;
  }
  info(0,"\ah%u arr vias",cumviacnt);
  afree0(arrmap);
  if (cumviacnt == 0) return error0(0,"no vias");

  net->deplst[1] = deplst;
  net->arrlst[1] = arrlst;
  net->depdurlst[1] = depdurlst;
  net->arrdurlst[1] = arrdurlst;

  if (netstop == 1) rmiadr(durlims);
  else finiadr(durlims);

  return 0;
}
