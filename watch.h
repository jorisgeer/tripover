// watch.h - watch item support

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014 Joris van der Geer.
 */

static ub8 rsids2log[8];
static ub4 rsid2logcnt;

static int rsid2log(ub4 rsid,ub4 lvl)
{
  ub4 r,i = 0;
  ub8 x;

  for (i = 0; i < rsid2logcnt; i++) {
    x = rsids2log[i];
    r = (ub4)x;
    if (r != rsid && r != hi32) continue;
    if ((x >> 32) >= lvl) return 1;
  }
  return 0;
}

#define rsidlog(rsid,fmt,...) rsidlogfln(FLN,(rsid),(fmt),__VA_ARGS__)

static int  __attribute__ ((format (printf,3,4))) rsidlogfln(ub4 fln,ub4 rsid,const char *fmt,...)
{
  va_list ap;
  char buf[2048];

  if (rsid2logcnt && rsid2log(rsid,0)) {
    va_start(ap, fmt);
    myvsnprintf(buf,0,sizeof(buf),fmt,ap);
    va_end(ap);
    infofln(fln,0,"rsid \ax%u: %s",rsid,buf);
    return 1;
  } else return 0;
}

static ub8 hops2log[8];
static ub4 hop2logcnt;

static int hop2log(ub4 hop,ub4 lvl)
{
  ub4 h,i = 0;
  ub8 x;

  while (i < hop2logcnt) {
    x = hops2log[i++];
    h = (ub4)x;
    if (h != hop && h != hi32) continue;
    if ((x >> 32) >= lvl) return 1;
  }
  return 0;
}

#define hoplog(hop,lvl,fmt,...) hoplogfln(FLN,(hop),(lvl),(fmt),__VA_ARGS__)

static int  __attribute__ ((format (printf,4,5))) hoplogfln(ub4 fln,ub4 hop,ub4 lvl,const char *fmt,...)
{
  va_list ap;
  char buf[2048];

  if (hop2logcnt && hop2log(hop,lvl)) {
    va_start(ap, fmt);
    myvsnprintf(buf,0,sizeof(buf),fmt,ap);
    va_end(ap);
    infofln(fln,0,"hop %u: %s",hop,buf);
    return 1;
  } else return 0;
}
