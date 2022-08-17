// math.c - math utilities

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014 Joris van der Geer.
 */

/* math utilities like statistics, geo, random
 */

#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <math.h>

#include "base.h"
#include "math.h"

static ub4 msgfile;
#include "msg.h"

#include "mem.h"
#include "util.h"
#include "time.h"

static int vrbena;

int minmax(ub4 *x, ub4 n, struct range *rp)
{
  ub4 lo = hi32;
  ub4 hi = 0;
  ub4 lopos = 0;
  ub4 hipos = 0;
  ub4 i,v;

  for (i = 0; i < n; i++) {
    v = x[i];
    if (v < lo) { lo = v; lopos = i; }
    if (v > hi) { hi = v; hipos = i; }
  }
  rp->hi = hi; rp->lo = lo;
  rp->hipos = hipos; rp->lopos = lopos;
  rp->hilo = hi - lo;
  return (n == 0);
}

int minmax2(ub2 *x, ub4 n, struct range *rp)
{
  ub4 lo = hi32;
  ub4 hi = 0;
  ub4 lopos = 0;
  ub4 hipos = 0;
  ub4 i,v;

  for (i = 0; i < n; i++) {
    v = x[i];
    if (v < lo) { lo = v; lopos = i; }
    if (v > hi) { hi = v; hipos = i; }
  }
  rp->hi = hi; rp->lo = lo;
  rp->hipos = hipos; rp->lopos = lopos;
  rp->hilo = hi - lo;
  return (n == 0);
}

int mkhist(ub4 callee,ub4 *data, ub4 n,struct range *rp, ub4 ivcnt,ub4 *bins, const char *desc,enum Msglvl lvl)
{
  ub4 lo,hi,i,v,iv;

  error_lt(ivcnt,2);
  error_z(n,0);

  minmax(data,n,rp);
  lo = rp->lo;
  hi = rp->hi;

  if (hi == lo) return info(0,"nil range for histogram %s", desc);

  info(0,"%s: lo %u hi \ah%u range %u",desc,lo,hi,hi - lo);

  memset(bins,0,ivcnt * sizeof(ub4));
  for (i = 0; i < n; i++) {
    v = data[i];
    if (v < lo) bins[ivcnt - 2]++;
    else if (v > hi) bins[ivcnt-1]++;
    else {
      if (v - lo >= hi32 / ivcnt) errorfln(callee,Exit,FLN,"val %u out of range lo %u bins %u",v,lo,ivcnt);
      iv = (v - lo) * (ivcnt - 2) / (hi - lo);
      error_ge(iv,ivcnt);
      bins[iv]++;
    }
  }
  for (iv = 0; iv < ivcnt; iv++) {
    genmsg(lvl,User,"bin %u: %u",iv,bins[iv]);
  }
  return 0;
}

int mkhist2(ub2 *data, ub4 n,struct range *rp, ub4 ivcnt,ub4 *bins, const char *desc,enum Msglvl lvl)
{
  ub4 lo,hi,i,v,iv,cnt,sum,csum;
  ub8 perc,ccnt;

  error_lt(ivcnt,2);
  error_z(n,0);

  minmax2(data,n,rp);
  lo = rp->lo;
  hi = rp->hi;

  if (hi == lo) return info(0,"nil range for histogram %s", desc);

  memset(bins,0,ivcnt * sizeof(ub4));
  sum = 0;
  for (i = 0; i < n; i++) {
    v = data[i];
    sum += v;
    if (v < lo) bins[ivcnt - 2]++;
    else if (v > hi) bins[ivcnt-1]++;
    else {
      iv = (v - lo) * (ivcnt - 2) / (hi - lo);
      error_ge(iv,ivcnt);
      bins[iv]++;
    }
  }
  info(User,"%s: %u bins avg %u sum %u", desc,ivcnt,sum / n,sum);
  csum = 0;
  for (iv = 0; iv < ivcnt; iv++) csum += bins[iv];

  ccnt = 0;
  for (iv = 0; iv < ivcnt; iv++) {
    cnt = bins[iv];
    ccnt += cnt;
    perc = ccnt * 100 / csum;
    genmsg(lvl,User,"  bin %u: %u %u%%", iv,cnt,(ub4)perc);
  }
  return 0;
}

// wikipedia xorshift
static ub8 xorshift64star(void)
{
  static ub8 x = 0x05a3ae52de3bbf0aULL;

  x ^= x >> 12; // a
  x ^= x << 25; // b
  x ^= x >> 27; // c
  return (x * 2685821657736338717ULL);
}

static ub8 rndstate[ 16 ];

static ub4 xorshift1024star(void)
{
  static int p;

  ub8 s0 = rndstate[p];
  ub8 s1 = rndstate[p = ( p + 1 ) & 15];
  s1 ^= s1 << 31; // a
  s1 ^= s1 >> 11; // b
  s0 ^= s0 >> 30; // c
  rndstate[p] = s0 ^ s1;

  return (ub4)(rndstate[p] * 1181783497276652981ULL);
}

static ub4 rndmask(ub4 mask) { return (ub4)xorshift1024star() & mask; }

ub4 rnd(ub4 range)
{
  ub4 r;
  if (range == 0) r = 1;
  else r = (ub4)xorshift1024star();
  if (range && range != hi32) r %= range;
  return r;
}

double frnd(ub4 range)
{
  double x;

  x = rnd(range);
  return x;
}

// diamond-square fractal landscape, after wikipedia and its links
int mkheightmap(ub4 *map,ub4 n)
{
  ub4 x,y,range,range1,len,len2;
  ub4 val00,val01,val10,val11,mval,cval0,cval1,cval2,cval3;

  len = n;
  len2 = len >> 1;
  range = (1 << 14);
  range1 = range - 1;

// seed 4 corners
/*
  map[0] = val0 + rnd(range1);
  map[n-1] = val0 + rnd(range1);
  map[n] = val0 + rnd(range1);
  map[n * n - 1] = val0 + rnd(range1);
*/
  do {
    if (range > 2) {
      range >>= 1;
      range1 = range - 1;
    }

    vrb(0,"len %u range %u",len,range);
    for (y = 0; y + len < n; y += len) {

      for (x = 0; x + len < n; x += len) {

        // diamond step
        val00 = map[y * n + x];
        val01 = map[(y + len) * n + x];
        val10 = map[y * n + x + len];
        val11 = map[(y + len) * n + x + len];
        mval = (val00 + val01 + val10 + val11) >> 2;
        mval += rndmask(range1);
        map[(y+len2) * n + x + len2] = mval;

        // square step
        cval0 = (val00 + val10 + mval) / 3;
        cval0 += rndmask(range1);
        map[(y + len2) * n + x] = cval0;

        cval1 = (val00 + val01 + mval) / 3;
        cval1 += rndmask(range1);
        map[y * n + x + len2] = cval1;

        cval2 = (val01 + val11 + mval) / 3;
        cval2 += rndmask(range1);
        map[(y + len2) * n + x + len] = cval2;

        cval3 = (val10 + val11 + mval) / 3;
        cval3 += rndmask(range1);
        map[(y + len) * n + x + len2] = cval3;
      }
    }
    len >>= 1;
    len2 >>= 1;
  } while(len);

//  writeppm("heightmap.ppm",map,n,n);

  return 0;
}

// lat,lon to distance functions and vars

double lat2rad(ub4 lat,ub4 scale)
{
  if (scale == 0) {
    error(0,"zero geo scale for lat %u",lat);
    return 1;
  }
  double deg = ((double)lat / (double)scale - 90.0);
  double r = deg * M_PI / 180.0;
  return r;
}

double lon2rad(ub4 lon,ub4 scale)
{
  if (scale == 0) {
    error(0,"zero geo scale for lon %u",lon);
    return 1;
  }
  double r = ((double)lon / (double)scale - 180.0) * M_PI / 180.0;
  return r;
}

ub4 rad2lat(double rlat,ub4 scale) { return (ub4)(( (rlat * 180 / M_PI) + 90) * scale); }
ub4 rad2lon(double rlon,ub4 scale) { return (ub4)(( (rlon * 180 / M_PI) + 180) * scale); }

// minlat,maxlat,latrange,minlon,maxlon,lonrange,midlat,midlon,count
void updbbox(ub4 lat,ub4 lon,ub4 *bbox,ub4 boxlen)
{
  error_lt(boxlen,Geocnt);

  if (bbox[Boxcnt] == 0) {
    bbox[Minlat] = bbox[Minlon] = hi32;
  }
  bbox[Minlat] = min(bbox[Minlat],lat);
  bbox[Maxlat] = max(bbox[Maxlat],lat);
  bbox[Minlon] = min(bbox[Minlon],lon);
  bbox[Maxlon] = max(bbox[Maxlon],lon);
  bbox[Latrng] = bbox[Maxlat] - bbox[Minlat];
  bbox[Lonrng] = bbox[Maxlon] - bbox[Minlon];
  bbox[Midlat] = bbox[Minlat] + bbox[Latrng] / 2;
  bbox[Midlon] = bbox[Minlon] + bbox[Lonrng] / 2;
  bbox[Boxcnt]++;
}

// static double geolow = M_PI * 2.0e-5;   // ~ 500 m
static double geolimit = M_PI * 2.0e-8;
// static double approx_earth_surface = 9009.955; // sqrt(radius^2 * 2)
static double mean_earth_radius = 6371.0;

/* great circle lat/lon to Km.
  Adapted from Wikipedia article http://en.wikipedia.org/wiki/Great-circle_distance
  tested with http://andrew.hedges.name/experiments/haversine/
*/
double geodistfln(double rlat1, double rlon1, double rlat2, double rlon2,ub4 fln)
{
//  double fdist, dlat, dlon;
  double d,phi1,phi2,lam1,lam2,dphi,dlam,dsig,dist;

  phi1 = rlat1;
  phi2 = rlat2;
  lam1 = rlon1;
  lam2 = rlon2;

  if (rlat1 <= -0.5 * M_PI || rlat1 >= 0.5 * M_PI) { errorfln(fln,0,FLN,"lat1 %e", rlat1); return Georange; }
  if (rlat2 <= -0.5 * M_PI || rlat2 >= 0.5 * M_PI) { errorfln(fln,0,FLN,"lat2 %e", rlat2); return Georange; }
  if (rlon1 < -M_PI || rlon1 > M_PI) { errorfln(fln,0,FLN,"lon1 %e", rlon1); return Georange; }
  if (rlon2 < -M_PI || rlon2 > M_PI) { errorfln(fln,0,FLN,"lon2 %e", rlon2); return Georange; }

  dlam = lam2 - lam1;
  dphi = phi2 - phi1;

  if (dlam > -geolimit && dlam < geolimit && dphi > -geolimit && dphi < geolimit) { // flush to 0
    // vrb0(0,"geodist 0 below |%e|",geolimit);
    return 0.0;
#if 0
  } else if (dlam > -geolow && dlam < geolow && dphi > -geolow && dphi < geolow) { // approx trivial case
    vrbcc(vrbena,0,"geodist trivial %e %e between |%e|",dlam,dphi,geolow);
    dlat = dlam * approx_earth_surface * 2 / M_PI;
    dlon = dphi * approx_earth_surface * 2 / M_PI;
    fdist = sqrt(dlat * dlat + dlon * dlon);
    return round(fdist * Geoscale);
#endif
  }

  d = sin(phi1) * sin(phi2) + cos(phi1) * cos(phi2) * cos(dlam);
  if (d >= 1.0) { warnfln2(fln,Iter,FLN,"geodist d %e for %e %e-%e %e",d,rlat1,rlon1,rlat2,rlon2); return 0.0; }
  else if (d <= -1.0) { warnfln2(fln,Iter,FLN,"geodist d %e for %e %e-%e %e",d,rlat1,rlon1,rlat2,rlon2); return Georange; }

  dsig = acos(d);

  if (isnan(dsig)) { errorfln(fln,0,FLN,"geodist %e %e-%e %e nan",rlat1,rlon1,rlat2,rlon2); return Georange; }

  dist = dsig * mean_earth_radius;

  return dist * Geoscale;
}

int inimath(void)
{
  ub8 x;

  msgfile = setmsgfile(__FILE__);
  iniassert();

  vrbena = (getmsglvl() >= Vrb);

  for (x = 0; x < 16; x++) rndstate[x] = xorshift64star();

  return 0;
}
