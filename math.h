// math.h

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014 Joris van der Geer.
 */

#ifndef M_PI
  #define M_PI 3.141592655
#endif

struct range {
  ub4 lo,hi,hilo;
  ub4 lopos,hipos;
};

extern int minmax(ub4 *x, ub4 n, struct range *rp);
extern int minmax2(ub2 *x, ub4 n, struct range *rp);
extern int mkhist(ub4 callee,ub4 *data, ub4 n,struct range *rp, ub4 ivcnt,ub4 *bins, const char *desc,ub4 lvl);
extern int mkhist2(ub2 *data, ub4 n,struct range *rp, ub4 ivcnt,ub4 *bins, const char *desc,ub4 lvl);

extern ub4 rnd(ub4 range);
extern double frnd(ub4 range);

extern int mkheightmap(ub4 *map,ub4 n);

extern double lat2rad(ub4 lat,ub4 scale);
extern double lon2rad(ub4 lon,ub4 scale);
extern ub4 rad2lat(double rlat,ub4 scale);
extern ub4 rad2lon(double rlon,ub4 scale);

enum Geobox {Minlat,Maxlat,Minlon,Maxlon,Latrng,Lonrng,Midlat,Midlon,Boxcnt,Geocnt};

extern void updbbox(ub4 lat,ub4 lon,ub4 *bbox,ub4 bboxlen);

#define geodist(a1,o1,a2,o2,s) geodistfln((a1),(o1),(a2),(o2),FLN)
extern double geodistfln(double rlat1, double rlon1, double rlat2, double rlon2,ub4 fln);

extern int inimath(void);
