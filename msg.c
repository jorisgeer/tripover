// msg.c - messages

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2016 Joris van der Geer.
 */

/* This file contains messaging logic used for 3 purposes:
   - console messages for the end user ( info, status, diagnostics)
   - debug logging
   - assertions

   As the program relies heavily on format flexibility, a custom print formatter
   is included here that is mostly compatible with printf, yet contains custom features

  assertions are used extensively, and are made to be enabled in production
 */

#include <stdarg.h>
#include <string.h>
#include <stdlib.h>
#include <ctype.h>
#include <math.h>

#include "base.h"

static ub4 msgfile;

#include "msg.h"

#include "os.h"
#include "util.h"
#include "time.h"

#undef hdrstop

struct filecoord {
  char name[16];
};

static struct filecoord filenames[Maxmsgfile];
static ub4 filendx = 1;
static enum Msgfileopts fileopts[Maxmsgfile];

static ub4 lastrow[Msglvl_last];
static ub4 currow;

static enum Msglvl msglvl = Vrb,prvlvl = Vrb;
static ub4 vrblvl = 2;
static ub4 msgopts;

static int msg_fd = -1;
static ub4 msgwritten;

static ub4 warncnt,errcnt,assertcnt,oserrcnt;

static const char msgnames[Msglvl_last] = "XFAEWIV ";
static const char *msgnames_long[Msglvl_last] = {
  "X",
  "fatal",
  "assert",
  "error",
  "warning",
  "info",
  "verbose","" };

#define MSGLEN 2048
#define Tmsglen MSGLEN * Nthread
static char gmsgbuf[Tmsglen];

static ub4 lastwarntoggle = 1;
static char lastwarn[Tmsglen];
static char lastwarn2[Tmsglen];
static char lasterr[Tmsglen];
static ub4 lastwarniter,lastwarn2iter;

#define Pfxlen 128
static char prefix[Nthread * Pfxlen];
static ub4 prefixlen;

static ub4 hicnts[Nthread * Msglvl_last];
static ub4 hiflns[Nthread * Msglvl_last];
static ub4 hicnts2[Nthread * Msglvl_last];
static ub4 hiflns2[Nthread * Msglvl_last];

static char himsgbufs[Msglvl_last][MSGLEN];
static char himsgbufs2[Msglvl_last][MSGLEN];

static ub4 decorpos;

static ub8 progstart;

static ub4 gitercnts[Nthread * Maxmsgfile * Maxmsgline];

static ub4 himsgcnts[Maxmsgfile * Maxmsgline];

static ub2 msgconfigs[Maxmsgfile * Maxmsgline];
static ub4 msgctimes[Maxmsgfile * Maxmsgline];

static int streq(const char *s,const char *q) { return !strcmp(s,q); }

static inline ub4 msgtid(ub4 code)
{
  code &= Tidmask;
  return (code >> Tidshift);
}

// temporary choice. unbuffered is useful for console messages,
// yet debug logging may ask for buffering
static void msgwrite(const char *buf,ub4 len,int notty)
{
  int nw;
  int fd = msg_fd < 0 ? 1 : msg_fd;
  char dbuf[64];
  ub4 dn;

  if (len == 0) return;

  msgwritten += len;

  ub4 i;
  for (i = 0; i < len; i++) {
    if (buf[i] == 0) oswrite(fd,"\n! null char in msg !\n",22);
  }

  nw = (int)oswrite(fd,buf,len);

  if (nw == -1 && !globs.background) {
    nw = (int)oswrite(2,"\nI/O error on msg write ",24);
    dn = myutoa(dbuf,len);
    oswrite(2,dbuf,dn);
    oswrite(2,"\n",1);
  }
  if (nw == -1) oserrcnt++;
  if (msg_fd > 2 && !notty && !globs.background) oswrite(1,buf,len);
}

void msg_write(const char *buf,ub4 len) { msgwrite(buf,len,0); }

static void msg_swrite(const char *buf)
{
  if (buf) msgwrite(buf,strlen4(buf),0);
}

static void msg_wrfln(ub4 fln)
{
  ub4 line = fln & 0xffff;
  ub4 fileno = fln >> 16;
  char lnbuf[16];
  ub4 n;

  msg_swrite(fileno < Elemcnt(filenames) ? filenames[fileno].name : "???");
  msg_swrite(" ");
  n = myutoa(lnbuf,line);
  msgwrite(lnbuf,n,0);
  msg_swrite(" ");
}

void msg_errwrite(ub4 fln,ub4 fln2,ub4 fln3,const char *buf)
{
  msg_swrite("\nE ");
  msg_wrfln(fln);
  if (fln2) msg_wrfln(fln2);
  if (fln3) msg_wrfln(fln3);

  errcnt++;

  if (buf) msg_swrite(buf);
}

// make errors appear on stderr
static void myttywrite(char *buf, ub4 len)
{
  int nw;

  if (len == 0 || globs.background) return;

  nw = (int)oswrite(2,buf,len);
  if (nw == -1) oserrcnt++;
}

// basic %x
static ub4 xcnv(char *dst, ub4 x,ub4 wid,char pad)
{
  ub4 n,nw=0,c,nib = 7;

  if (x < 0x10) n = 1;
  else if (x < 0x100) n = 2;
  else if (x < 0x1000) n = 3;
  else if (x < 0x10000) n = 4;
  else if (x < 0x100000) n = 5;
  else if (x < 0x1000000) n = 6;
  else if (x < 0x10000000) n = 7;
  else n = 8;

  while (wid > n++) { *dst++ = pad; nw++; }

  while (nib) {
    c = (x >> (nib * 4)) & 0xf;
    if (c) break;
    nib--;
  }
  while (nib) {
    c = (x >> (nib * 4)) & 0xf;
    c += '0';
    if (c > '9') c += ('a' - '9') - 1;
    *dst++ = (char)c;
    nw++;
    nib--;
  }
  c = (x & 0xf) + '0';
  if (c > '9') c += ('a' - '9') - 1;
  *dst++ = (char)c;
  *dst = '?';

  return nw+1;
}

// basic %u
static ub4 ucnv(char *dst, ub4 x,ub4 wid,char pad)
{
  ub4 n,nn;

  if (x < 10) n = 1;
  else if (x < 100) n = 2;
  else if (x < 1000) n = 3;
  else if (x < 10000) n = 4;
  else if (x < 100000) n = 5;
  else if (x < 1000000) n = 6;
  else if (x < 10000000) n = 7;
  else if (x < 100000000) n = 8;
  else if (x < 1000000000) n = 9;
  else n = 10;

  nn = n;
  if (wid > n) {
    while (wid > nn) { *dst++ = pad; nn++; }
  }
  memset(dst,' ',n);
  dst += n;
  do *--dst = (ub1)((x % 10) + '0'); while (x /= 10);
  return nn;
}

ub4 myutoa(char *dst,ub4 x) { return ucnv(dst,x,0,' '); }

// human-readable %u, 12.3G
static ub4 Ucnv(char *dst, ub4 x1,ub4 x2,char c)
{
  ub4 n;

  if (x1 < 10) n = 1;
  else if (x1 < 100) n = 2;
  else if (x1 < 1000) n = 3;
  else if (x1 < 10000) n = 4;
  else n = 5;

  if (x2) n += 3;

  dst += n + 1;
  *dst-- = c;
  *dst-- = ' ';

  if (x2) { // print 2 decimals
    if ((x2 % 10) > 5) x2 += 10;
    x2 /= 10;
    x2 = min(x2,99);
    *dst-- = (ub1)((x2 % 10) + '0'); x2 /= 10;
    *dst-- = (ub1)((x2 % 10) + '0');
    *dst-- = '.';
  }
  do *dst-- = (ub1)((x1 % 10) + '0'); while (x1 /= 10);
  return n + 2;
}

// basic %lu
static ub4 lucnv(char *dst, ub8 x,ub4 wid,char pad)
{
  ub4 n = 0,nn;
  ub8 t = x;

  do n++; while (t /= 10);

  nn = n;
  if (wid > n) {
    while (wid > nn) { *dst++ = pad; nn++; }
  }
  memset(dst,' ',n);
  dst += n;
  do *--dst = (ub1)((x % 10) + '0'); while (x /= 10);
  return nn;
}

// simple %e
static ub4 ecnv(char *dst, double x)
{
  double fexp,exp;
  ub4 xscale;
  ub4 nmant,n = 0;
  char *org = dst;
  char mantissa[32];

  if (isnan(x)) { memcpy(dst,"#NaN",4); return 4; }
  else if (isinf(x)) { memcpy(dst,"#Inf",4); return 4; }

  if (x < 0) { *dst++ = '-'; x = -x; }
  if (x < 1.0e-200) { *dst++ = '~'; *dst++ = '0'; return (ub4)(dst - org); }

  fexp = log10(x);
  if (fexp < 0) {     // |x| < 1.0
    exp = floor(fexp);
    x *= pow(10,-exp);
  } else if (fexp >= 1) { // |x| >= 10.0
    exp = floor(fexp);
    x /= pow(10,exp);
  } else {
    exp = 0;
  }
  xscale = (ub4)(x * 1.0e+6);
  memcpy(mantissa,"??????",6);
  nmant = ucnv(mantissa,xscale,0,0);
  *dst++ = mantissa[0];
  *dst++ = '.';
  if (nmant < 2) { nmant = 6; }
  memcpy(dst,mantissa + 1,nmant - 1);
  dst += nmant - 1;
  *dst++ = 'e';
  if (exp < 0) { *dst++ = '-'; exp = -exp; }
  else *dst++ = '+';
  n = ucnv(dst,(ub4)exp,0,0);

  n += (ub4)(dst - org);
  return n;
}

// simple %f
static ub4 fcnv(char *dst, ub4 len,double x)
{
  double fexp,exp;
  ub4 iexp;
  ub4 ix,n = 0,pos = 0;

  if (len < 24) return len;

  // trivia
  if (isnan(x)) { memcpy(dst,"#NaN",4); return 4; }
  else if (isinf(x)) { memcpy(dst,"#Inf",4); return 4; }
  else if (x > -1e-7 && x < 1e-7) { *dst = '0'; return 1; }
  else if (x < -4e9) { *dst++ = '-'; n = 1 + ucnv(dst,hi32,0,' '); return n; }
  else if (x > 4e9) return ucnv(dst,hi32,0,' ');

  if (x < 0) { dst[pos++] = '-'; x = -x; }

  fexp = log10(x);
  if (fexp < 0) {     // |x| < 1.0
    if (fexp < -7) { dst[pos] = '0'; return n + 1; }

    exp = floor(fexp);
    iexp = (ub4)-exp;

    dst[pos++] = '0'; dst[pos++] = '.';
    while (iexp > 1 && len - pos > 2) { dst[pos++] = '0'; if (iexp) iexp--; }

    x *= 1e7;

    if (x > 1) {
      if (len - pos < 16) return len;
      ix = (ub4)x;
      pos += ucnv(dst + pos,ix,0,'0');
    }
  } else { // |x| >= 1.0
    ix = (ub4)x;
    pos += ucnv(dst + pos,ix,0,'0');
    dst[pos++] = '.';
    x = (x - ix) * 1e+7;
    ix = (ub4)x;
    pos += ucnv(dst + pos,ix,7,'0');
  }
  return pos;
}

/* supports a subset of printf plus compatible extensions :
   %c %d %u %x %e %f %s %p %03u %-12.6s %ld %*s
   extensions are led in by '\a' preceding a conversion :
   0   end if next arg not 0
   d + %u  minute utc to date 20140912
   D + %u  minute utc to date 20140912
   g + %u  distance in m or Km, passed geo units
   h + %u  makes the integer formatted 'human readable' like 123.8 M for 123800000
   p + %lu,%lu percentage or promillage
   r + %f radians in degrees
   s   adds plural 's' if last arg not 1
   t + %u  duration in minutes
   u + %u  utc offset +0930   -1100
   v + %u%p interprets the pointer arg '%p' as an array of '%u' integers. thus :
     int arr[] = { 23,65,23,54 };  printf("\av%u%p", 4, arr );
     shows  '[23 65 23 54]'
   x + %u  %x.%u
   ` + %s  replace , with `
 */

static ub4 bufovf(ub4 fln,ub4 fln2,fln3,ub4 len,ub4 pos)
{
  char vp_buf1[32];
  char vp_buf2[32];

  msg_errwrite(fln,fln2,fln3,"vsnprint len ");
  vp_n1 = ucnv(vp_buf1,len,0,' ');
  msgwrite(vp_buf1,vp_n1,0);

  msg_swrite(" pos ");
  vp_n2 = ucnv(vp_buf2,len,0,' ');
  msgwrite(vp_buf2,vp_n2,0);

  return 0;
}

#define vsnprint(l,d,p,n,f,a) vsnprint_fln(FLN,(l),(d),(p),(n),(f),(a))

static ub4 vsnprint_fln(ub4 fln,ub4 fln2,char *dst, ub4 pos, ub4 len, const char *fmt, va_list ap)
{
  const char *p = fmt;
  ub4 orglen = len;
  ub4 n = 0,prvn = 0,x;
  ub4 wid,prec,uprec = 0,plen;
  ub4 dd,hh,mm,mdist,kmdist;
  unsigned int uval=0,prvuval=0,vlen=0,cdval,*puval;
  unsigned long luval,prvluval = 0,lx,perc_v1 = 0,perc,perm;
  int ival,alt,padleft,do_U = 0,do_vec = 0,do_mindate = 0,do_utcofs = 0,do_xu = 0,do_dot = 0;
  int do_comma = 0,do_dist = 0,do_mindur = 0,do_perc = 0,do_rad = 0,do_0 = 0,do_eq = 0;
  long lival;
  double dval;
  char *pval;
  char c,c1,c2;
  char pad = ' ';
  double rad2deg = 180.0 / M_PI;

  char vp_buf1[32];
  char vp_buf2[32];
  ub4 vp_n1,vp_n2;

  if (!p) return msg_errwrite(FLN,fln,fln2,"vsnprint nil fmt\n");
  else if (*p == 0) return msg_errwrite(FLN,fln,fln2,"vsnprint empty fmt\n");

  if (len < 2) {
    msg_errwrite(FLN,fln,fln2,"vsnprint len ");
    vp_n1 = ucnv(vp_buf1,len,0,' ');
    msgwrite(vp_buf1,vp_n1,0);
    msg_swrite(" min 2/n");
    return 0;
  }
  len--;
  dst[len] = 0;

  if (pos >= len || len - pos < 2) {
    msg_errwrite(FLN,fln,fln2,"vsnprint len ");
    vp_n1 = ucnv(vp_buf1,pos,0,' ');
    msgwrite(vp_buf1,vp_n1,0);

    msg_swrite(" pos ");
    vp_n2 = ucnv(vp_buf2,len,0,' ');
    msgwrite(vp_buf2,vp_n2,0);
    msg_swrite(" < 2\n");
    return 0;
  }

  len -= pos; dst += pos; len--;

  while (*p && len - n > 2) {
    c1 = *p++;

    // extensions
    if (c1 == '\a') {
      switch(*p++) {
        case '0': do_0 = 1; prvn = n; break;
        case '=': do_eq = 1; prvn = n; break;
        case 'h': do_U = 1; break;
        case 'v': do_vec = 1; break;
        case 'V': do_vec = 2; break;
        case '.': do_dot = 1; break;
        case 'g': do_dist = 1; break;
        case 't': do_mindur = 1; break;
        case 'u': do_utcofs = 1; break;
        case 'd': do_mindate = 1; break;
        case 'r': do_rad = 1; break;
        case 'D': do_mindate = 2; break;
        case 'p': do_perc = 1; break;
        case 'x': do_xu = 1; break;
        case '`': do_comma = 1; break;
        case 's': if (uval != 1) dst[n++] = 's'; break;
        case '%': dst[n++] = c1; break;
        default: dst[n++] = c1;
      }
      c1 = *p; if (c1) p++;
    }
    if (c1 == '%') {
      wid = 0; pad = ' '; padleft = 0;
      prec = len; uprec = 0;
      c2 = *p++;
      if (c2 == '-') { padleft = 1; c2 = *p++; }
      if (c2 == '*') {
        wid = va_arg(ap,unsigned int);
        c2 = *p++;
        if (wid == 0) {
          msg_errwrite(fln,FLN,0,"nul width");
          msg_errwrite(fln,FLN,0,fmt);
        }
      }
      if (c2 == '0') pad = c2;
      while (c2 >= '0' && c2 <= '9') {
        wid = wid * 10 + (c2 - '0');
        c2 = *p++;
      }
      wid = min(wid,len - n);
      alt = 0;
      if (c2 == '#') { alt = 1; c2 = *p++; }
      else if (c2 == '.') {
        c2 = *p++;
        if (c2 == '*') { prec = va_arg(ap,unsigned int); c2 = *p++; }
        else {
          prec = 0;
          while (c2 >= '0' && c2 <= '9') {
            prec = prec * 10 + (c2 - '0');
            c2 = *p++;
          }
          uprec = prec;
        }
      }

      // all long formats
      if (c2 == 'l') {

        if (len - n < 24) return bufovf(FLN,fln,fln2,len,n);

        c2 = *p++;
        switch(c2) {

        case 'u': luval = va_arg(ap,unsigned long);
                  if (do_0) {
                    do_0 = 0;
                    if (luval == 0) { dst[prvn] = 0; return prvn; }
                  } else if (do_eq) {
                    do_eq = 0;
                    if (luval == prvluval) { dst[prvn] = 0; return prvn; }
                  }
                  prvluval = luval;
                  uval = (ub4)min(luval,hi32);

                  if (do_perc == 1) {  // store first arg
                    perc_v1 = luval;
                    do_perc = 2;
                    break;
                  } else if (do_perc == 2) {
                    do_perc = 0;
                    if (perc_v1 == hi64 || luval == hi64 || perc_v1 >= luval || luval == 0) perc = 100;
                    else perc = (perc_v1 * 100UL) / luval;
                    perc = min(perc,100);
                    if (perc == 0) {
                      dst[n++] = '0';
                      dst[n++] = '.';
                      perm = (perc_v1 * 1000UL) / luval;
                      n += ucnv(dst + n,(ub4)perm,wid,pad);
                    } else {
                      n += ucnv(dst + n,(ub4)perc,wid,pad);
                    }
                    dst[n++] = '%';
                    break;
                  } else if (luval == hi16) {
                    memcpy(dst + n,"hi16",4); n += 4;
                  } else if (luval == hi32) {
                    memcpy(dst + n,"hi32",4); n += 4;
                  } else if (luval == hi64) {
                    memcpy(dst + n,"hi64",4); n += 4;
                  } else if (do_U && luval >= 1024UL * 10) {
                    lx = luval;
                    if (lx == hi32) n += Ucnv(dst + n,4,0,'G');
                    else if (lx >= 1024UL * 1024UL * 1024UL) n += Ucnv(dst + n,(ub4)(lx >> 30),(ub4)(lx >> 20) & 0x3ff,'G');
                    else if (lx >= 1024UL * 1024UL) n += Ucnv(dst + n,(ub4)(lx >> 20),(ub4)(lx >> 10) & 0x3ff,'M');
                    else n += Ucnv(dst + n,(ub4)(lx >> 10),(ub4)lx & 0x3ff,'K');
                  } else if (luval > hi32) {
                    n += lucnv(dst + n,luval,wid,pad);
#if 0
                    n += ucnv(dst + n,(ub4)(luval >> 32),wid,pad);
                    dst[n++] = ',';
                    n += ucnv(dst + n,(ub4)luval,wid,pad);
#endif
                  } else n += ucnv(dst + n,(ub4)luval,wid,pad);
                  break;
        case 'x':
        case 'p': luval = va_arg(ap,unsigned long);
                  uval = (ub4)min(luval,hi32);
                  if (luval > hi32) {
                    n += xcnv(dst + n,(ub4)(luval >> 32),wid - min(wid,8),pad);
                    n += xcnv(dst + n,(ub4)luval,8,'0');
                  } else n += xcnv(dst + n,(ub4)luval,wid,pad);
                  break;
        case 'd':
                  lival = va_arg(ap,long);
                  if (lival == 1) uval = 1;
                  else uval = hi32;
                  if (lival < 0) { dst[n++] = '-'; n += ucnv(dst + n, (ub4)-lival,wid,pad); }
                  else n += ucnv(dst + n, (ub4)lival,wid,pad);
                  break;
        case 'e': dval = va_arg(ap,double);
                  if (len - n <= 12) break;
                  n += ecnv(dst + n,dval);
                  break;
        case 'f': dval = va_arg(ap,double);
                  n += fcnv(dst + n,len - n,dval);
                  if (len - n < 8) return bufovf(FLN,fln,fln2,len,n);
                  break;
        default: dst[n++] = c2;
        }

      // all non-long formats, including extensions
      } else {
        switch(c2) {

        case 'u': if (len - n < 24) return bufovf(FLN,fln,fln2,len,n);

                  uval = va_arg(ap,unsigned int);
                  if (do_0) {
                    do_0 = 0;
                    if (uval == 0) { dst[prvn] = 0; return prvn; }
                  } else if (do_eq) {
                    do_eq = 0;
                    if (uval == prvuval) { dst[prvn] = 0; return prvn; }
                  }
                  prvuval = uval;

                  if (do_vec) { vlen = uval; break; }  // save len for vector fmt

                  else if (do_dist) { // distance in geo units to Km or m
                    do_dist = 0;
                    if (uval == hi32 || uval == hi32 - 1) { dst[n++] = '-'; break; }
                    mdist = geo2m(uval);
                    kmdist = mdist / 1000;
                    if (mdist >= 5000) {
                      n += ucnv(dst + n,kmdist,wid,pad);
                      mdist %= 1000;
                      if (mdist) {
                        dst[n++] = '.';
                        n += ucnv(dst + n,(mdist % 1000) / 100,1,'0');
                      }
                      dst[n++] = ' '; dst[n++] = 'K'; dst[n++] = 'm';
                    } else if (mdist >= 1000) {
                      n += ucnv(dst + n,kmdist,wid,pad);
                      mdist %= 1000;
                      if (mdist) {
                        dst[n++] = '.';
                        n += ucnv(dst + n,mdist / 10,2,'0');
                      }
                      dst[n++] = ' '; dst[n++] = 'K'; dst[n++] = 'm';
                    } else {
                      n += ucnv(dst + n,mdist,wid,pad);
                      dst[n++] = ' '; dst[n++] = 'm';
                    }
                    break;

                  // dotted 123.454
                  } else if (do_dot) {
                    do_dot = 0;
                    if (uval >= 1000 * 1000) {
                      n += ucnv(dst + n,uval / 1000000,wid,'0'); dst[n++] = '.';
                      uval %= 1000000;
                      wid = 3;
                    }
                    if (uval >= 1000) {
                      n += ucnv(dst + n,uval / 1000,wid,'0'); dst[n++] = '.';
                      uval %= 1000;
                      wid = 3;
                    }
                    n += ucnv(dst + n,uval,wid,'0');
                    break;

                  // coded decimal or standard date/time
                  } else if (do_mindate) {
                    if (do_mindate == 2) {
                      n += ucnv(dst + n,uval,wid,pad);
                      dst[n++] = ' ';
                    }
                    do_mindate = 0;

                    if (uval < 1440 * 365) { // relative minutes
                      hh = uval / 60; mm = uval % 60;
                      x = hh * 100 + mm;
                      n += ucnv(dst + n,x,0,' ');
                    } else if (uval < 20000101) { // minutes since epoch
                      cdval = lmin2cd(uval);
                      n += ucnv(dst + n,cdval,4,'0');
                      uval %= 1440;
                      if (uval) {
                        dst[n++] = '.';
                        hh = uval / 60; mm = uval % 60;
                        x = hh * 100 + mm;
                        n += ucnv(dst + n,x,4,'0');
                      }
                    } else { // yyyymmdd
                      cdval = day2cd(uval);
                      n += ucnv(dst + n,cdval,wid,pad);
                    }
                    break;

                  } else if (do_mindur) {  // time duration in minutes
                    do_mindur = 0;
                    if (uval == hi32) { dst[n++] = '-'; break; }
                    if (uval >= 2 * 1440) {
                      dd = uval / 1440;
                      n += ucnv(dst + n,dd,wid,pad);
                      memcpy(dst + n," days",5); n += 5;
                      uval %= 1440;
                    }
                    if (uval == 0) break;
                    dst[n++] = ' ';
                    hh = uval / 60; mm = uval % 60;
                    if (uval >= 60) {
                      n += ucnv(dst + n,hh,wid,pad);
                      memcpy(dst + n," hour",5); n += 5;
                      if (hh > 1) dst[n++] = 's';
                      if (mm == 0) break;
                    }
                    dst[n++] = ' ';
                    n += ucnv(dst + n,mm,wid,pad);
                    memcpy(dst + n," min ",5); n += 5;
                    break;

                  // utc (timezone) offset
                  } else if (do_utcofs) {
                    do_utcofs = 0;
                    if (uval > (14 + 12) * 60) { dst[n++] = '!'; uval = (14+12) * 60; }
                    if (uval < 12 * 60) { dst[n++] = '-'; uval = 12 * 60 - uval; }
                    else { dst[n++] = '+'; uval -= 12 * 60; }
                    n += ucnv(dst + n,uval / 60,2,'0');
                    dst[n++] = ':';
                    n += ucnv(dst + n,uval % 60,2,'0');
                    break;
                  } else if (do_xu) {
                    do_xu = 0;
                    n += xcnv(dst + n,uval,wid,pad);
                    if (len - n <= 10) break;
                    dst[n++] = '.';
                  }

                  // human-readable 12.3M
                  if (do_U && uval >= 1024U * 10) {
                    x = uval;
                    if (x == hi32) n += Ucnv(dst + n,4,0,'G');
                    else if (x >= 1024U * 1024 * 2) n += Ucnv(dst + n,x >> 20,(x >> 10) & 0x3ff,'M');
                    else n += Ucnv(dst + n,x >> 10,x & 0x3ff,'K');

                  // regular
                  } else if (uval == hi16) {
                    memcpy(dst + n,"hi16",4); n += 4;
                  } else if (uval == hi32) {
                    memcpy(dst + n,"hi32",4); n += 4;
                  } else n += ucnv(dst + n,uval,wid,pad);
                  break;

        case 'x': if (len - n < 16) return bufovf(FLN,fln,fln2,len,n);
                  uval = va_arg(ap,unsigned int);
                  if (alt) { dst[n++] = '0'; dst[n++] = 'x'; }
                  n += xcnv(dst + n,uval,wid,pad);
                  break;

        case 'd': if (len - n < 16) return bufovf(FLN,fln,fln2,len,n);
                  ival = va_arg(ap,int);
                  if (ival == 1) uval = 1;
                  else uval = hi32;
                  if (ival < 0) { dst[n++] = '-'; n += ucnv(dst + n, -ival,wid,pad); }
                  else n += ucnv(dst + n,ival,wid,pad);
                  break;

        case 'e': if (len - n < 16) return bufovf(FLN,fln,fln2,len,n);
                  dval = va_arg(ap,double);
                  if (do_rad) dval *= rad2deg;
                  n += ecnv(dst + n,dval);
                  break;

        case 'f': if (len - n < 16) return bufovf(FLN,fln,fln2,len,n);
                  dval = va_arg(ap,double);
                  if (do_rad) dval *= rad2deg;
                  n += fcnv(dst + n,len - n,dval);
                  if (len - n < 16) return bufovf(FLN,fln,fln2,len,n);
                  break;

        case 'c': if (len - n < 8) return bufovf(FLN,fln,fln2,len,n);
                  uval = va_arg(ap,unsigned int);
                  if (isprint(uval)) dst[n++] = (char)uval;
                  else {
                    dst[n++] = '0'; dst[n++] = 'x';
                    if (len - n <= 10) break;
                    n += xcnv(dst + n,uval & 0xff,wid,pad);
                    dst[n++] = ' ';
                  }
                  break;

        case 's': if (len - n < 2) return bufovf(FLN,fln,fln2,len,n);

                  pval = va_arg(ap,char *);
                  if (prec == 0) break;

                  if (!pval) return msg_errwrite(FLN,fln,fln2,"vsnprint nil arg for %s\n");
                  else if ((size_t)pval < 4096) return msg_errwrite(FLN,fln,fln2,"vsnprint int arg for %s\n");
                  else if ((size_t)pval == hi32) return msg_errwrite(FLN,fln,fln2,"vsnprint int arg '-1' for %s\n");
                  else if ((size_t)pval == hi64) return msg_errwrite(FLN,fln,fln2,"vsnprint long arg '-1' for %s\n");

                  plen = 0; while (plen < prec && plen + n < len && pval[plen]) plen++;
                  if (do_comma) {
                    while ( (c = *pval++) && n < len && prec--) dst[n++] = (c == ',' ? '`' : c);
                  } else if (padleft) {
                    while (*pval && n < len && prec--) dst[n++] = *pval++;
                    while (wid > plen && n < len) { dst[n++] = pad; wid--; }
                  } else {
                    while (wid > plen && n < len) { dst[n++] = pad; wid--; }
                    while (n < len && prec && *pval) { dst[n++] = *pval++; prec--; }
                    if (uprec && prec == 0 && *p && n && (dst[n-1] & 0x80)) {
                      while (n && (dst[n-1] & 0xc0) == 0x80) n--; // avoid partial utf-8 char
                      if (n && (dst[n-1] & 0xc0) == 0xc0) n--;
                    }
                    if (uprec && prec == 0 && *pval && n + 3 < len) {
                      dst[n++] = (char)0xE2U; // utf-8 ellipsis
                      dst[n++] = (char)0x80U;
                      dst[n++] = (char)0xA6U;
                    }
                  }
                  break;

        case 'p': puval = va_arg(ap,unsigned int *);
                  if (do_vec) {
                    if (len - n < 16) return bufovf(FLN,fln,fln2,len,n);
                    n += ucnv(dst + n,vlen,0,0);
                    dst[n++] = '.'; dst[n++] = '[';
                    while (vlen) {
                      uval = *puval++;
                      if (len - n < 16) return bufovf(FLN,fln,fln2,len,n);
                      n += ucnv(dst + n,uval,wid,pad);
                      if (do_vec == 2) {
                        if (len - n < 16) return bufovf(FLN,fln,fln2,len,n);
                        dst[n++] = '.';
                        uval = *puval++;
                        n += ucnv(dst + n,uval,wid,pad);
                      }
                      if (--vlen) dst[n++] = '-';
                    }
                    dst[n++] = ']'; dst[n++] = ' ';
                    do_vec = 0;
                  } else {
                    if (len - n < 20) return bufovf(FLN,fln,fln2,len,n);
                    luval = (unsigned long)puval;
                    if (luval == 0) {
                      memcpy(dst + n,"(nil)",5);
                      n += 5;
                      break;
                    }
                    if (sizeof(char *) > 4 && luval > hi32) n += xcnv(dst + n,(unsigned int)(luval >> 32),wid,pad);
                    n += xcnv(dst + n,(unsigned int)(luval & hi32),wid,pad);
                  }
                  break;

        default: if (len - n < 2) return bufovf(FLN,fln,fln2,len,n);
                 dst[n++] = c2;
        }
      }
      do_U = do_rad = 0;
    } else if (c1) {
      if (len - n < 2) return bufovf(FLN,fln,fln2,len,n);
      dst[n++] = c1;
    }
  }
  dst[n] = 0;

  return n;
}

ub4 myvsnprintf_fln(ub4 fln,char *dst, ub4 pos, ub4 len, const char *fmt, va_list ap)
{
  return vsnprint(fln,dst,pos,len,fmt,ap);
}

ub4 __attribute__ ((format (printf,7,8))) mysnprintf_fln(ub4 fln,char *dst,ub4 pos,ub4 len,const char *spos,const char *slen,const char *fmt,...)
{
  va_list ap;
  ub4 n;

  if (pos >= len) return warnfln2(fln,0,FLN,"snprintf: pos %s:%u >= len %s:%u",spos,pos,slen,len);
  va_start(ap, fmt);
  n = vsnprint(fln,dst,pos,len,fmt,ap);
  va_end(ap);
  if (n == 0) {
    msg_swrite(fmt);
    msg_swrite("");
  }
  return n;
}

static ub4 callstack[64];
static ub4 callpos;

void enter(ub4 fln)
{
  if (callpos + 1 < Elemcnt(callstack)) callstack[callpos++] = fln;
  else infofln(fln,0,"enter above callstack");
}

extern void leave(ub4 fln)
{
  if (callpos) callpos--;
  else infofln(fln,0,"leave below callstack");
}

static void showstack(void)
{
  ub4 pos,cpos = callpos;
  char buf[256];

  while (cpos) {
    pos = msgfln(buf,0,sizeof(buf)-1,callstack[--cpos],9);
    buf[pos++] = '\n';
    msgwrite(buf,pos,0);
  }
}

// print file coords only
ub4 msgfln(char *dst,ub4 pos,ub4 len,ub4 fln,ub4 wid)
{
  ub4 line = fln & hi16;
  ub4 fileno = fln >> 16;

  if (wid == 0) wid = 2;
  if (fileno < Elemcnt(filenames)) return mysnprintf(dst,pos,len, "%*s %-4u ",wid,filenames[fileno].name,line);
  return mysnprintf(dst,pos,len, "*%7x* %-4u ",fileno,line);
}

static void msginfo(ub4 fln,ub4 code)
{
  char buf[1024];
  char xfile[32];
  ub4 len;

  ub4 tid = msgtid(code);
  if (tid || (code & User)) return;

  ub4 line = fln & 0xffff;
  ub4 fileno = fln >> 16;
  ub8 now_usec,dusec,d100usec;
  ub4 dsec,dss,dmm,dhh;
  char *filename;

  if (fileno >= Maxmsgfile) {
    msg_errwrite(FLN,fln,0,"file above max\n");
    return;
  }
  if (line >= Maxmsgline) {
    msg_errwrite(FLN,fln,0,"line above max\n");
    return;
  }

  himsgcnts[min(fileno,Maxmsgfile - 1) * Maxmsgline | min(line,Maxmsgline - 1)]++;

  now_usec = gettime_usec();
  dusec = now_usec - progstart;
  dsec = (ub4)(dusec / (1000 * 1000));
  d100usec = (dusec % (1000 * 1000)) / 100;
  dss = dsec % 60;
  dmm = (dsec / 60) % 60;
  dhh = dsec / 3600;

  if (fileno >= Elemcnt(filenames)) {
    fmtstring(xfile,"*%x",fileno);
    filename = xfile;
  } else filename = filenames[fileno].name;

  if (dhh) len = fmtstring(buf,"X %u.%02u.%02u.%04u %9s %4u\n",dhh,dmm,dss,(ub4)d100usec,filename,line);
  else if (dmm) len = fmtstring(buf,"X %02u.%02u.%04u %9s %4u\n",dmm,dss,(ub4)d100usec,filename,line);
  else len = fmtstring(buf,"X %02u.%04u %9s %4u\n",dss,(ub4)d100usec,filename,line);
  setmsginfo(buf,len);
}

// main message printer. supports decorated and undecorated style
static int msg(enum Msglvl lvl, ub4 sublvl, ub4 fline, ub4 code, const char *fmt, va_list ap)
{
  ub4 opts;
  ub4 pos = 0,dpos,maxlen = MSGLEN;
  sb4 n = 0;
  ub8 now_usec,dusec,d100usec;
  ub4 dsec,dss,dmm,dhh;
  ub4 lvlnam;
  ub4 iter,iterndx,itercnt,iterlim,file,line;
  static ub4 himsgcnt[Maxmsgline * Maxmsgfile];
  ub4 tt,atidcnt = 0,tid = msgtid(code);
  ub4 *itercnts = gitercnts + tid * Maxmsgfile * Maxmsgline;
  char *msgbuf = gmsgbuf + tid * MSGLEN;
  char dbuf[256];
  int rv = 0;

  if (fmt == NULL) {
    dpos = fmtstring0(dbuf,"msg(): nil fmt\n");
    msg_errwrite(fline,FLN,0,dbuf);
    fmt = "(nil fmt)";
    lvl = Error;
    rv = 1;
  }
  if ((size_t)fmt < 4096) {
    dpos = fmtstring(dbuf,"msg(): int fmt %p\n",(const void *)fmt);
    msg_errwrite(fline,FLN,0,dbuf);
    fmt = "(int fmt)";
    lvl = Error;
    rv = 1;
  }

  prvlvl = lvl;

  if (code & User) {
    code &= ~User;
    code |= Noiter;
    opts = 0;
  } else opts = msgopts;

  file = min(fline >> 16,Maxmsgfile-1);
  line = fline & hi16;
  iterndx = min(line,Maxmsgline-1);

  iter = itercnts[file * Maxmsgline | iterndx];
  itercnt = iter & hi24;
  if (itercnt < hi24 && opts) {
    itercnt++;
    itercnts[file * Maxmsgline | iterndx] = itercnt | (lvl << 24);
  }
  if (fileopts[file] & Msgfile_noiter) iterlim = hi24;
  else if (code & Iter) iterlim = 50;
  else if (code & Noiter) iterlim = hi24;
  else iterlim = 500;

  if (itercnt > iterlim) return rv;
  else if (itercnt == iterlim) pos += mysnprintf(msgbuf,pos,maxlen, "  message at line %u repeated %u times\n",iterndx,itercnt);

  if (opts & Msg_stamp) {
    now_usec = gettime_usec();
    dusec = now_usec - progstart;
    dsec = (ub4)(dusec / (1000 * 1000));
    d100usec = (dusec % (1000 * 1000)) / 100;
    dss = dsec % 60;
    dmm = (dsec / 60) % 60;
    dhh = dsec / 3600;
  } else { d100usec = 0; dss = dmm = dhh = 0; }
  if (lvl >= Msglvl_last) {
    pos += mysnprintf(msgbuf,pos,maxlen, "\nE unknown msglvl %u\n",lvl);
    lvl = Error;
    rv = 1;
  }

  lastrow[lvl] = ++currow;

  lvlnam = msgnames[lvl];

  if (*fmt == '\n') {
    msgbuf[pos++] = '\n';
    fmt++;
  }
  if (opts & Msg_type) {
    if (sublvl) lvlnam += 0x20;
    if (assertcnt && assertcnt >= errcnt && (lvl > Assert || assertcnt > 1)) pos += mysnprintf(msgbuf, pos, maxlen, "A %u ",assertcnt);
    else if (errcnt) pos += mysnprintf(msgbuf, pos, maxlen, "E %u ",errcnt);
    pos += mysnprintf(msgbuf, pos, maxlen, "%c",lvlnam);
    msgbuf[pos++] = (code & Emp ? '\\' : ' ');
  } else if (lvl <= Warn) {
    pos += mysnprintf(msgbuf, pos, maxlen, "%s",msgnames_long[lvl]);
    msgbuf[pos++] = (code & Emp ? '\\' : ' ');
  }

  if (globs.tidcnt > 1 && (code & Tidbit)) {
    for (tt = 0; tt < min(Nthread,globs.tidcnt * 2); tt++) { if (globs.tids[tt]) atidcnt++; }
    pos += mysnprintf(msgbuf, pos, maxlen, "%2u/%u ",tid,atidcnt);
  }

  if (opts & Msg_stamp) {
    if (dhh) pos += mysnprintf(msgbuf, pos, maxlen, "%u.%02u.%02u.%04u ",dhh,dmm,dss,(ub4)d100usec);
    else if (dmm) pos += mysnprintf(msgbuf, pos, maxlen, "%02u.%02u.%04u ",dmm,dss,(ub4)d100usec);
    else pos += mysnprintf(msgbuf, pos, maxlen, "%02u.%04u ",dss,(ub4)d100usec);
  }
  if (opts & Msg_pos) {
    pos += msgfln(msgbuf,pos,maxlen,fline,9);
  }

  if (code & Ind) {
    n = min(code & Indent, maxlen - pos);
    if (n) memset(msgbuf + pos,' ',n);
    pos += n;
  }
  if (prefixlen && (code & Nopfx) == 0 && pos + prefixlen < maxlen) {
    memcpy(msgbuf + pos,prefix,prefixlen);
    pos += prefixlen;
    if (pos + 1 < maxlen) msgbuf[pos++] = ' ';
  }
  if (lvl <= Error) prefixlen = 0;

  decorpos = pos;

  pos += vsnprint(fline,msgbuf,pos,maxlen,fmt,ap);
  pos = min(pos,maxlen-1);
  msgbuf[pos] = 0;

  ub4 cnt;
  if (tid == 0 && *fmt && opts) {
    iter = himsgcnt[file * Maxmsgline | iterndx];
    cnt = iter & hi24;
    if (cnt < hi24) {
      cnt++;
      himsgcnt[file * Maxmsgline | iterndx] = cnt | (lvl << 24);
    }
    if (cnt > hicnts[lvl]) {
      hicnts[lvl] = cnt;
      hiflns[lvl] = fline;
      memcpy(himsgbufs[lvl],msgbuf,pos+1);
    } else if (cnt > hicnts2[lvl] && fline != hiflns[lvl]) {
      hicnts2[lvl] = cnt;
      hiflns2[lvl] = fline;
      memcpy(himsgbufs2[lvl],msgbuf,pos+1);
    }

    if (lvl == Warn) {
      if (lastwarntoggle) {
        memcpy(lastwarn,msgbuf,pos);
        lastwarn[pos] = 0;
        lastwarniter = cnt;
      } else {
        memcpy(lastwarn2,msgbuf,pos);
        lastwarn2[pos] = 0;
        lastwarn2iter = cnt;
      }
      lastwarntoggle ^= 1;
    }
    else if (lvl < Warn && !(code & (Exit|EXit))) { memcpy(lasterr,msgbuf,pos); lasterr[pos] = 0; }
  }
  msgbuf[pos++] = '\n';
  msgwrite(msgbuf,pos,code & Notty);
  if ( (code & Msg_ccerr) && lvl <= Warn && msg_fd != 2) myttywrite(msgbuf,pos);
  return rv;
}

void vmsg(enum Msglvl lvl,ub4 fln,const char *fmt,va_list ap)
{
  msg(lvl,0,fln,0,fmt,ap);
}

// exit if configured e.g. assertions
Noret static void ccexit(int assertion,ub4 code,ub4 fln)
{
  ub4 orgerrcnt = errcnt;

  errcnt = 0;
  if (assertion == 0) infofln2(fln,0,FLN,"exit on code %x",code);
  errcnt = orgerrcnt;
  eximsg(0);
  msg_swrite("rv=1\n");
  exit(1);
}

int __attribute__ ((format (printf,4,5))) genmsgfln(ub4 fln,enum Msglvl lvl,ub4 code,const char *fmt,...)
{
  va_list ap;
  ub4 slvl = (code / V0) & 3;

  msginfo(fln,code);

  if (msglvl < lvl) return 0;
  if (vrblvl < slvl) return 0;

  va_start(ap, fmt);
  msg(lvl, slvl, fln, code, fmt, ap);
  va_end(ap);
  return (lvl < Warn);
}

int __attribute__ ((format (printf,2,3))) msgprefix(int rv,const char *fmt, ...)
{
  va_list ap;

  if (fmt == NULL || *fmt == 0) { prefixlen = 0; return rv; }

  va_start(ap, fmt);
  prefixlen = vsnprint(0,prefix,0,sizeof(prefix),fmt,ap);
  // if (prefixlen < sizeof(prefix)) prefix[prefixlen++] = ' ';
  va_end(ap);
  return rv;
}

int __attribute__ ((format (printf,3,4))) vrbfln(ub4 fln, ub4 code, const char *fmt, ...)
{
  va_list ap;
  ub4 lvl = (code / V0) & 3;
  int rv = (code & Ret1) ? 1 : 0;
  enum Msglvl lim = Vrb;
  ub4 file = fln >> 16;
  ub4 line = fln & hi16;
  ub4 optndx = file * Maxmsgline + line;
  char optbuf[64];

  if (optndx >= Maxmsgfile * Maxmsgline) {
    char buf[1024];
    fmtstring(buf,"fln %u.%u above max %u.%u",fln >> 16,fln & hi16,Maxmsgfile,Maxmsgline);
    msg_errwrite(FLN,fln,0,buf);
    return rv;
  }

  ub4 opt = msgconfigs[optndx];
  if (opt & 0x8000) {
    lvl = 0;
    lim = opt & 0x7f;
    if (lim >= Msglvl_last) {
      msg_errwrite(FLN,fln,0,"unknown msg level\n");
      lim = Fatal;
    }
    if (lim < Vrb) {
      fmtstring(optbuf,"V -> %c\n",msgnames[lim]);
      msg_swrite(optbuf);
    }
  }

  msginfo(fln,code);

  if (msglvl < lim) return rv;
  if (vrblvl < lvl) return rv;

  va_start(ap, fmt);
  msg(lim, lvl, fln, code, fmt, ap);
  va_end(ap);
  return rv;
}

static int iscc0(ub4 fln,va_list ap,const char *fmt)
{
  const char *p = strchr(fmt,'%');
  int i;
  long l;

  if (p == NULL) return errorfln(FLN,0,fln,"CC0 without arg in %s",fmt);
  p++;
  while (*p && (*p != 'u' && *p != 'd' && *p != 'x')) {
    if (*p == 'l') {
      l = va_arg(ap,long);
      return (l != 0);
    }
    p++;
  }
  i = va_arg(ap,int);
  return (i != 0);
}

int __attribute__ ((format (printf,3,4))) infofln(ub4 fln, ub4 code, const char *fmt, ...)
{
  va_list ap;
  int i;
  ub4 lvl = (code / V0) & 3;
  int rv = (code & Ret1) ? 1 : 0;
  ub4 file = fln >> 16;
  ub4 line = fln & hi16;
  ub4 optndx = file * Maxmsgline + line;
  char optbuf[64];

  enum Msglvl lim = Info;

  if (optndx >= Maxmsgfile * Maxmsgline) {
    msg_errwrite(FLN,fln,0,"fln above max\n");
    return rv;
  }

  ub4 opt = msgconfigs[optndx];
  if (opt & 0x8000) {
    lvl = 0;
    lim = opt & 0x7f;
    if (globs.strict && lim > Info) lim = Info;
    if (lim >= Msglvl_last) {
      msg_errwrite(FLN,fln,0,"unknown msg level\n");
      lim = Fatal;
    }
    if (lim < Info) {
      fmtstring(optbuf,"I -> %c\n",msgnames[lim]);
      msg_swrite(optbuf);
    }
  }

  msginfo(fln,code);

  if (msglvl < lim) return rv;
  if (vrblvl < lvl) return rv;

  if ((code & CC0) && lim > Error) {
    va_start(ap, fmt);
    i = iscc0(fln,ap,fmt);
    va_end(ap);
    if (i == 0) return rv;
  }

  va_start(ap, fmt);
  msg(lim, lvl, fln, code, fmt, ap);
  va_end(ap);
  if ( (code & (Exit|EXit)) || lim < Error) ccexit(0,code,fln);
  return rv;
}

int __attribute__ ((format (printf,4,5))) infofln2(ub4 line,ub4 code,ub4 fln2,const char *fmt,...)
{
  va_list ap;
  int i;
  ub4 lvl = (code / V0) & 3;
  int rv = (code & Ret1) ? 1 : 0;

  msginfo(line,code);
  if (msglvl < Info) return rv;
  if (vrblvl < lvl) return rv;

  if (code & CC0) {
    va_start(ap, fmt);
    i = iscc0(line,ap,fmt);
    va_end(ap);
    if (i == 0) return rv;
  }

  va_start(ap, fmt);

  if (fln2) msg(Nolvl,0,fln2,Noiter,"",NULL);
  msg(Info,0,line,code,fmt,ap);
  va_end(ap);
  if (code & (Exit|EXit)) ccexit(0,code,line);
  return rv;
}

int info0fln(ub4 line, ub4 code, const char *s)
{
  msginfo(line,code);
  if (msglvl < Info) return 0;
  return infofln(line, code, "%s", s);
}

int warn0fln(ub4 line, ub4 code, const char *s)
{
  msginfo(line,code);
  if (msglvl < Warn) return 0;
  return warnfln(line, code, "%s", s);
}

int __attribute__ ((format (printf,3,4))) warnfln(ub4 line, ub4 code, const char *fmt, ...)
{
  va_list ap;
  int i;
  int rv = (code & Ret1) ? 1 : 0;

  msginfo(line,code);
  if (msglvl < Warn) return rv;

  if (code & CC0) {
    va_start(ap, fmt);
    i = iscc0(line,ap,fmt);
    va_end(ap);
    if (i == 0) return rv;
  }

  warncnt++;
  va_start(ap, fmt);
  msg(Warn, 0, line, code, fmt, ap);
  va_end(ap);
  if (code & (Exit|EXit)) ccexit(0,code,line);
  return rv;
}

int __attribute__ ((format (printf,4,5))) warnfln2(ub4 line,ub4 code,ub4 fln2,const char *fmt,...)
{
  va_list ap;
  int i;
  int rv = (code & Ret1) ? 1 : 0;

  msginfo(line,code);
  if (msglvl < Warn) return rv;

  if (code & CC0) {
    va_start(ap, fmt);
    i = iscc0(line,ap,fmt);
    va_end(ap);
    if (i == 0) return rv;
  }

  warncnt++;
  va_start(ap, fmt);

  if (fln2) msg(Nolvl,0,fln2,Nopfx,"",NULL);
  msg(Warn, 0, line, code, fmt, ap);
  va_end(ap);
  if (code & (Exit|EXit)) ccexit(0,code,line);
  return rv;
}

Noret int __attribute__ ((format (printf,4,5))) fatalfln(ub4 fln,ub4 code,ub4 fln2,const char *fmt, ...)
{
  va_list ap;

  if (fln2) msg(Nolvl,0,fln2,Nopfx,"",NULL);
  va_start(ap, fmt);
  msg(Fatal,0,fln,code,fmt,ap);
  va_end(ap);
  errcnt++;
  ccexit(0,code,fln);
}

int __attribute__ ((format (printf,4,5))) errorfln(ub4 fln,ub4 code,ub4 fln2,const char *fmt, ...)
{
  va_list ap;
  int i;

  if (code & CC0) {
    va_start(ap, fmt);
    i = iscc0(fln,ap,fmt);
    va_end(ap);
    if (i == 0) return 0;
  }

  if (fln2) msg(Nolvl,0,fln2,Nopfx,"",NULL);
  va_start(ap, fmt);
  msg(Error, 0, fln, code, fmt, ap);
  va_end(ap);
  errcnt++;
  if (code & (Exit|EXit)) ccexit(0,code,fln);
  else if (code & Ret0) return 0;
  return 1;
}

void * __attribute__ ((format (printf,4,5))) nilerrfln(ub4 fln,ub4 code,ub4 fln2,const char *fmt, ...)
{
  va_list ap;

  if (fln2) msg(Nolvl,0,fln2,0,"",NULL);
  va_start(ap, fmt);
  msg(Error, 0, fln, code, fmt, ap);
  va_end(ap);
  errcnt++;
  if (code & (Exit|EXit)) ccexit(0,code,fln);
  return NULL;
}

Noret void __attribute__ ((format (printf,3,4))) assertfln(ub4 line, ub4 code, const char *fmt, ...)
{
  va_list ap;

  showstack();

  assertcnt++;

  va_start(ap, fmt);
  msg(Assert, 0, line, code, fmt, ap);
  va_end(ap);
  ccexit(1,code,line);
}

int __attribute__ ((format (printf,3,4))) osinfofln(ub4 line,ub4 code,const char *fmt, ...)
{
  va_list ap;
  char *errstr = getoserr();
  char buf[MSGLEN];

  msginfo(line,code);
  if (msglvl < Info) return 0;

  va_start(ap, fmt);
  vsnprint(line,buf,0,sizeof(buf),fmt,ap);
  va_end(ap);
  return infofln(line,code,"%s: %s",buf,errstr);
}

int __attribute__ ((format (printf,3,4))) oswarningfln(ub4 line,ub4 code,const char *fmt, ...)
{
  va_list ap;
  char *errstr = getoserr();
  char buf[MSGLEN];

  msginfo(line,code);
  warncnt++;
  if (msglvl < Warn) return 0;

  va_start(ap, fmt);
  vsnprint(line,buf,0,sizeof(buf),fmt,ap);
  va_end(ap);
  return warnfln(line,code,"%s: %s",buf,errstr);
}

int oswarn0fln(ub4 line, ub4 code, const char *s)
{
  char *errstr = getoserr();

  msginfo(line,code);
  if (msglvl < Warn) return 0;
  return warnfln(line, code, "%s: %s",s,errstr);
}

int __attribute__ ((format (printf,3,4))) oserrorfln(ub4 line,ub4 code,const char *fmt, ...)
{
  va_list ap;
  char *errstr = getoserr();
  char buf[MSGLEN];

  va_start(ap, fmt);
  vsnprint(line,buf,0,sizeof(buf),fmt,ap);
  va_end(ap);
  return errorfln(line,code,0,"%s: %s",buf,errstr);
}

int __attribute__ ((format (printf,4,5))) oserrorfln2(ub4 fln,ub4 code,ub4 fln2,const char *fmt, ...)
{
  va_list ap;
  char *errstr = getoserr();
  char buf[MSGLEN];

  va_start(ap, fmt);
  vsnprint(fln,buf,0,sizeof(buf),fmt,ap);
  va_end(ap);
  return errorfln(fln,code,fln2,"%s: %s",buf,errstr);
}

ub4 limit_gt_fln(ub4 x,ub4 lim,ub4 arg,const char *sx,const char *slim,const char *sarg,ub4 fln)
{
  if (lim == 0) assertfln(fln,Exit,"zero limit %s for %s",sx,slim);
  if (x < lim - 1) return x;
  if (x == lim - 1) {
    warnfln(fln,0,"limiting %s:%u to %s:%u for %s:%u",sx,x,slim,lim,sarg,arg);
    return x;
  }
  return lim;
}

// todo convert to error_xx_cc_fln()
Noret void __attribute__ ((format (printf,7,8))) error_cc_fln(size_t a,size_t b,const char *sa,const char *sb,const char *cc,ub4 line,const char *fmt,...)
{
  va_list ap;
  int rv;

  va_start(ap,fmt);
  rv = msg(Info,0,FLN,Noiter,fmt,ap);
  va_end(ap);
  if (rv == 0) rv = info(Noiter,"'%s' %s '%s'",sa,cc,sb);
  if (rv == 0) assertfln(line,Noiter,"%lu %s %lu",a,cc,b);
  ccexit(1,0,line);
}

Noret void __attribute__ ((format (printf,5,6))) error_eq_cc_fln(size_t b,const char *sa,const char *sb,ub4 line,const char *fmt,...)
{
  va_list ap;
  int rv;

  va_start(ap,fmt);
  rv = msg(Info,0,line,User|Noiter|Ind|Nopfx|decorpos,fmt,ap);
  va_end(ap);
  if (rv) ccexit(1,0,line);

  int intconst = (*sb >= '0' && *sb <= '9');
  int ishi32 = streq(sb,"hi32");
  if (intconst | ishi32) assertfln(line,0,"%s == %lu", sa,b);
  else assertfln(line,0,"%s == %s:%lu", sa,sb,b);
}

Noret void __attribute__ ((format (printf,6,7))) error_ge_cc_fln(size_t a,size_t b,const char *sa,const char *sb,ub4 line,const char *fmt,...)
{
  va_list ap;
  int rv;

  va_start(ap,fmt);
  rv = msg(Info,0,line,User|Noiter|Ind|Nopfx|decorpos,fmt,ap);
  va_end(ap);
  if (rv == 0) assertfln(line,0,"%s:%lu >= %s:%lu", sa,a,sb,b);
  ccexit(1,0,line);
}

Noret void __attribute__ ((format (printf,7,8))) error_gt_cc_fln(ub4 code,size_t a,size_t b,const char *sa,const char *sb,ub4 line,const char *fmt,...)
{
  va_list ap;
  int rv;

  va_start(ap,fmt);
  rv = msg(Info,0,line,User|Noiter|Ind|Nopfx|decorpos,fmt,ap);
  va_end(ap);
  if (rv == 0) assertfln(line,code,"%s:%lu > %s:%lu", sa,a,sb,b);
  ccexit(1,0,line);
}

int __attribute__ ((format (printf,7,8))) Attribute(nonnull)
progress2(ub4 tid,ub4 tidcnt,struct eta *eta,ub4 fln,ub8 cur,ub8 end,const char *fmt, ...)
{
  va_list ap;
  ub8 sec = 1000 * 1000,dt,est,now = gettime_usec();
  ub4 hh,mm;
  ub4 mperc,perc;
  char buf[256];
  ub4 iv,pos,len = sizeof(buf);
  ub4 msgtid;
  ub4 tt,atidcnt = 1;
  int noimm = 0;

  if (*fmt == '-') { noimm = 1; fmt++; }

  if (tidcnt > 1) {
    msgtid = (tid << Tidshift) | Tidbit;
    for (tt = 1; tt < min(Nthread,globs.tidcnt * 2); tt++) { if (globs.tids[tt]) atidcnt++; }
  } else msgtid = 0;

  if (globs.sigint) {
    va_start(ap,fmt);
    msg(Info,msgtid,fln,0,fmt,ap);
    va_end(ap);
    if (tid == 0) msgprefix(0,NULL);
    infofln(fln,msgtid,"interrupted at \ah%lu from \ah%lu",cur,end);
    return 1;
  }

  if (cur == 0) {
    eta->cur = eta->end = 0;
    eta->limit = 0;
    eta->showcnt = 0;
    eta->stamp = eta->start = now;
  }
  if (eta->showcnt < 20) iv = 1;
  else if (eta->showcnt < 40) iv = 2;
  else iv = 10;
  iv *= atidcnt;

  if (noimm || cur + 1 < end || cur > end) {
    if ( (cur || noimm) && now - eta->stamp < iv * sec) return 0;
  }
  eta->stamp = now;

  va_start(ap,fmt);
  pos = vsnprint(fln,buf,0,len,fmt,ap);
  va_end(ap);
  mperc = (ub4)(((unsigned long)cur * 1000) / max(end,1));
  mperc = min(mperc,1000);

  dt = (now - eta->start) / sec;
  if (mperc == 0) est = 0;
  else if (mperc == 1000) est = 0;
  else {
    dt = dt * 1000 / mperc;
    est = (dt * (1000UL - mperc)) / 1000;
  }
  if (mperc > 925) eta->showcnt = 0;
  perc = mperc / 10;
  if (est == 0) mysnprintf(buf,pos,len," %u%% ...",perc);
  else if (est < 180) mysnprintf(buf,pos,len," %u%% ~%u sec",perc,(ub4)est);
  else if (est <= 600) mysnprintf(buf,pos,len," %u%% ~%u min %u sec",perc,(ub4)(est / 60),(ub4)(est % 60));
  else if (est <= 3600) mysnprintf(buf,pos,len," %u%% ~%u min",perc,(ub4)(est / 60));
  else {
    hh = (ub4)(est / 3600);
    mm = (ub4)(est % 3600) / 60;
    mysnprintf(buf,pos,len," %u%% ~%u hr %u min",perc,hh,mm);
  }
  infofln(fln,Noiter|Nopfx|msgtid,"%s",buf);
  eta->showcnt++;

  ub4 line = fln & 0xffff;
  ub4 fileno = fln >> 16;
  ub4 cmd;
  char cmdname[256];
  struct myfile mf;

  oclear(mf);

  if (fileno >= Elemcnt(filenames)) return 0;
  fmtstring(cmdname,"progcmd-%s-%u.cmd",filenames[fileno].name,line);
  if (fileexists(cmdname) == 0) return 0;
  if (readfile(&mf,cmdname,0,4096)) return 1;
  fileremove(cmdname);
  if (mf.len == 0) return 0;
  if (str2ub4(mf.buf,&cmd)) return 0;
  return cmd;
}

int setmsglog(const char *dir,const char *name,int newonly,int show)
{
  char logname[256];
  int fd,oldfd = msg_fd;
  int c,rv = 0;
  char *oldlines;
  long nr;
  ub4 n;

  aclear(gitercnts);

  if (streq(name,"-")) {
    globs.msg_fd = msg_fd = 1;
    strcopy(globs.logname,name);
    return 0;
  } else if (streq(name,"--")) {
    globs.msg_fd = msg_fd = 2;
    strcopy(globs.logname,name);
    return 0;
  }
  if (dir && *dir) fmtstring(logname,"%s/%s-%u.log",dir,name,globs.id);
  else fmtstring(logname,"%s-%u.log",name,globs.id);

  if (newonly == 0) {
    if (oldfd) infovrb(show,0,"opening %slog in %s",oldfd ? "new " : "",logname);
    for (c = 9; c; c--) {
      if (filerotate(logname,(const char)((c - 1) + '0'), (const char)(c + '0'))) return 1;
    }
    if (filerotate(logname,0,'0')) return 1;
  }

  fd = oscreate(logname);

  if (fd == -1) { rv = oserror(0,"cannot create logfile %s",logname); fd = 2; }
  else if (oldfd > 2 && msgwritten && newonly == 0 && globs.sigint == 0) {
    if (osrewind(oldfd)) rv = oserror(0,"cannot rewind %s",globs.logname);
    n = msgwritten;
    oldlines = malloc(n);
    memset(oldlines,' ',n);
    nr = osread(oldfd,oldlines,n);
    if (nr != (long)n) rv = oserror(0,"cannot read %s: %ld",globs.logname,nr);
    oswrite(fd,oldlines,n);
    osclose(oldfd);
    free(oldlines);
  }
  msgwritten = 0;

  globs.msg_fd = msg_fd = fd;
  if (oldfd && newonly == 0) infovrb(show,0,"opened new log in %s from %s",logname,globs.logname);
  strcopy(globs.logname,logname);
  return rv;
}

void clriters(void)
{
  nclear(gitercnts,Maxmsgfile * Maxmsgline);
}

static int dia_fd;

// level to be set beforehand
int inimsg(char *progname, const char *logname, ub4 opts)
{
  char dianame[1024];

  sassert(Nthread <= (Tidbit >> Tidshift),"tidbit accomodates nthread ");

  fmtstring(dianame,"%s-%u.dia",globs.progname,globs.id);

  // redirect stderr to file : prevent clang/gcc sanitizer output mix with our logging
  dia_fd = oscreate(dianame);
  if (dia_fd != -1) osdup2(dia_fd,2);

  progstart = gettime_usec();

  msgopts = opts;
  msgfile = setmsgfile(__FILE__);

  int nobck = (opts & Msg_bcklog) ? 0 : 1;
  setmsglog(NULL,logname,nobck,opts & Msg_show);

  infofln(0,Notty|User,"pid\t%d\tfd\t%d", globs.pid,globs.msg_fd); //on line 1:  used by dbg script

  infocc(msg_fd >= 0,Notty,"opening log %s for %s\n", logname,progname);

  iniassert();
  return 0;
}

static void showrep(ub4 ndx)
{
  ub4 x,cnt,file,line,fln;
  enum Msglvl lvl;

  x = gitercnts[ndx];
  cnt = x & hi24;
  lvl = x >> 24;
  if (lvl == Info && cnt < 100) return;
  if (lvl == Vrb && cnt < 200) return;
  if (cnt < 3) return;
  file = ndx / Maxmsgline;
  line = ndx % Maxmsgline;
  fln = file << 16 | line;
  genmsgfln(fln,lvl,0,"..repeated \ah%u times",cnt);
}

static void showhi(enum Msglvl lvl,ub4 lim)
{
    if (hicnts[lvl] > lim) infofln(hiflns[lvl],User,"%s *%u",himsgbufs[lvl],hicnts[lvl]);
    if (hicnts2[lvl] > lim) infofln(hiflns2[lvl],User,"%s *%u",himsgbufs2[lvl],hicnts2[lvl]);
}

void msgsum(bool warnonly)
{
  ub4 i,n,n0,n1,n2,i0,i1,i2;

  prefixlen = 0;

  if (warnonly && errcnt == 0 && assertcnt == 0 && warncnt == 0) return;

  if (errcnt == 0 && assertcnt == 0 && globs.nomsgsum == 0) {

    showhi(Warn,5);
    if (warnonly == 0) {
      showhi(Info,100);
      showhi(Vrb,500);
    }

    i0 = i1 = i2 = n0 = n1 = n2 = 0;
    for (i = 0; i < Maxmsgfile * Maxmsgline; i++) {
      n = gitercnts[i] & hi24;
      if (n > n0) { n0 = n; i0 = i; }
      else if (n > n1) { n1 = n; i1 = i; }
      else if (n > n2) { n2 = n; i2 = i; }
    }

    showrep(i0);
    showrep(i1);
    showrep(i2);

  }
  if (warncnt && assertcnt == 0 && errcnt == 0 && currow - lastrow[Warn] > 5) info(0,"\ah%u warning\as\n%s\n%s",warncnt,lastwarn,warncnt > 1 ? lastwarn2 : "");

  if (assertcnt && currow - lastrow[Assert] > 5) info(0,"\ah%u assertion\as",assertcnt);
  if (errcnt && currow - lastrow[Error] > 5) {
//    info(0,"rows %u,%u",currow,lastrow[Error]);
    info(0,"%u error\as\n%s",errcnt,lasterr);
  }
  if (oserrcnt && (errcnt > 1 || prvlvl != Error)) info(0,"%u I/O error\as",oserrcnt);
}

void eximsg(bool cnts)
{
  ub4 i,n;
  int fd;

  msgsum(0);

  // write overall msg counts
  char *filename;
  char buf[256];
  ub4 cnt,line,fileno;
  int mfd;

  fmtstring(buf,"%s-%u.msg",globs.progname,globs.id);
  if (cnts) {
    mfd = filecreate(buf,0);
    if (mfd != -1) {
      for (i = 0; i < Maxmsgline * Maxmsgfile; i++)
      {
        cnt = himsgcnts[i];
        if (cnt == 0) continue;
        fileno = i / Maxmsgline;
        line = i % Maxmsgline;
        filename = filenames[fileno].name;
        n = fmtstring(buf,"%s\t%u\t%u\n",filename,line,cnt);
        oswrite(mfd,buf,n);
      }
      osclose(mfd);
    }
  }

  fd = globs.msg_fd;
  if (fd != -1) { osclose(fd); globs.msg_fd = msg_fd = -1; }
}

void setmsglvl(enum Msglvl lvl,ub4 vlvl)
{
  msglvl = lvl;
  vrblvl = vlvl;
}

enum Msglvl getmsglvl(void) { return msglvl; }

// adjust message level by config
int msgopt_fln(ub4 fln,const char *name)
{
  ub4 file = fln >> 16;
  ub4 line = fln & hi16;
  ub4 optndx = file * Maxmsgline + line;
  ub4 otime;
  char var[1024];
  char c;
  struct myfile mf;

  error_ge(line,Maxmsgline);
  error_ge(file,Maxmsgfile);

  ub4 now = gettime_sec();

//  info(0,"file %u line %u %x",file,line,fln);

  ub2 opt = msgconfigs[optndx];

  otime = msgctimes[optndx];

  if (now <= otime || now - otime < 2) return 0;
  msgctimes[optndx] = now;

  fmtstring(var,"cfg/%s.%s",filenames[file].name,name);
  if (readfile(&mf,var,0,4096)) return 1;
  if (mf.exist == 0) { freefile(&mf); return info(0,"%s not present",var); }
  else if (mf.len == 0) { freefile(&mf); return info(0,"%s is empty",var); }

  c = mf.buf[0];
  freefile(&mf);

  switch(c) {
  case 'v': opt = Vrb; break;
  case 'i': opt = Info; break;
  case 'w': opt = Warn; break;
  case 'e': opt = Error; break;
  case 'f': opt = Fatal; break;
  default: return error(0,"%s: unknown msg level '%c'",var,c);
  }
  opt |= 0x8000;
  msgconfigs[optndx] = opt;
  return info(0,"%s -> %c",var,c);
}

// make assert and debug calls more compact
ub4 setmsgfile2(const char *filename,enum Msgfileopts opt)
{
  char *ext;
  struct filecoord *fc;
  ub4 len;

  if (filendx + 1 >= Elemcnt(filenames)) return 0;
  ext = strrchr(filename,'.');
  fc = filenames + filendx;
  if (ext) len = (ub4)(ext - filename);
  else len = (ub4)strlen(filename);
  len = min(len,sizeof(fc->name) - 1);
  memcpy(fc->name,filename,len);
  fileopts[filendx] = opt;
  return (filendx++ << 16);
}

ub4 setmsgfile(const char *filename)
{
  return setmsgfile2(filename,Msgfile_none);
}
