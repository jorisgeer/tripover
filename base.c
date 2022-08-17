// base.c - generic base utility functions

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2016 Joris van der Geer.
 */

#include <string.h>
#include <stdlib.h>

#include "base.h"

#define Chkfmt
static ub4 msgfile;
#include "msg.h"

ub4 str2ub4(const char *s, ub4 *pv)
{
  unsigned long n;

  char *ep;
  const char *s1 = s;

  *pv = 0;
  if (!s || !*s) return 0;
  while (*s1 == '0') {
    s1++;
    if (*s1 < '0' || *s1 > '9') return (ub4)(s1 - s);
  }
  n = strtoul(s1,&ep,10);
  if (ep == s1) return (ub4)(s1 - s);
  if (n > hi32) *pv = hi32;
  else *pv = (ub4)n;
  return (ub4)(ep - s);
}

ub4 bstr2ub4(const char *s, ub4 *pv)
{
  unsigned long n;

  char *ep;

  *pv = 0;
  if (!s || !*s) return 0;
  n = strtoul(s,&ep,2);
  if (ep == s) return 0;
  if (n > hi32) *pv = hi32;
  else *pv = (ub4)n;
  return (ub4)(ep - s);
}

ub4 hex2ub4(const char *s, ub4 *pv)
{
  unsigned long n;
  char *ep;

  *pv = 0;
  if (!s || !*s) return 0;
  n = strtoul(s,&ep,16);
  if (ep == s) return 0;
  if (n > hi32) *pv = hi32;
  else *pv = (ub4)n;
  return (ub4)(ep - s);
}

int hex2ub8(const char *s, ub8 *pv)
{
  unsigned long n;
  char *ep;

  *pv = 0;
  if (!s || !*s) return 1;
  n = strtoul(s,&ep,16);
  if (ep == s) return 1;
  *pv = n;
  return 0;
}

int str2dbl(const char *s,ub4 len,double *pv)
{
  char buf[256];
  char *d,*endp;
  ub4 n = 0;
  double v;

  len = min(len,sizeof(buf)-1);
  d = buf;
  while (n < len && s[n]) { d[n] = s[n]; n++; }
  buf[n] = 0;

  v = strtod(buf,&endp);
  *pv = 0;
  if (endp == buf) return 1;
  *pv = v;
  return 0;
}

ub4 strlen4(const char *s)
{
  if (s == NULL) return 0;
  size_t n = strlen(s);
  return (ub4)n;
}

void memcopyfln(void *dst,const void *src,size_t len,ub4 fln)
{
  char *d = dst;
  const char *s = src;

  if (len == 0) infofln(fln,0,"zero copy");
  else if (s < d && s + len > d) errorfln(fln,Exit,FLN,"overlapping copy: %p %p %lu",src,dst,(unsigned long)len);
  else if (s > d && d + len > s) errorfln(fln,Exit,FLN,"overlapping copy: %p %p %lu",src,dst,(unsigned long)len);
  else memcpy(dst,src,len);
}

void do_clear(void *p,size_t len) { memset(p,0,len); }
void do_sethi(void *p,size_t len) { memset(p,0xff,len); }

int strcompfln(const char *a,const char *b,const char *sa,const char *sb,ub4 fln)
{
  vrbfln(fln,0,"cmp %s %s",sa,sb);
  if (a == NULL) return errorfln(fln,Exit,FLN,"strcmp(%s:nil,%s",sa,sb);
  else if (b == NULL) return errorfln(fln,Exit,FLN,"strcmp(%s,%s:nil",sa,sb);
  else return strcmp(a,b);
}

int strncpyfln(char *dst,const char *src,ub4 len,const char *sdst,const char *ssrc,ub4 fln)
{
  const char *s = src;
  char *d = dst;
  ub4 n = 0;

  error_z(len,fln & hi16);
  error_lt(len,4);
  error_ep_fln(dst,src,sdst,ssrc,fln);
  len--;
  while (*s && n < len) {
    *d++ = *s++;
    n++;
  }
  *d = 0;
  if (n == len) warnfln2(FLN,0,fln,"strncpy overflows %u for %s",len,dst);

  return 0;
}

ub4 sat32(ub8 x,ub8 y)
{
  ub8 xy = x * y;
  return (ub4)min(xy,hi32);
}

ub4 msb(ub8 x)
{
  ub4 b = 0;
  while (x) { b++; x >>= 1; }
  return b;
}

ub4 cntbits(ub4 x)
{
  ub4 n = 0;
  while (x) {
    if (x & 1) n++;
    x >>= 1;
  }
  return n;
}

int inibase(void)
{

  msgfile = setmsgfile(__FILE__);
  iniassert();

  return 0;
}
