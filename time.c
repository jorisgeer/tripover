// time.c

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2016 Joris van der Geer.
 */

/* Logic dealing with wall-clock time
   Conversions, formatting, timezones

   Internal standard is minutes UTC since Epoch, typ 2000
   This is kept in an unsigned 32 bit integer
   UTC offset is minutes plus 12 hours kept as an unsigned integer.
   weekdays start at monday = 0 .. sunday = 6

   in some places a 'coded decimal' unsigned integer is used for a date
 */

#include <time.h>

#include "base.h"
#include "util.h"
#include "mem.h"
#include "time.h"

static ub4 msgfile;
#include "msg.h"

#include "os.h"

static ub4 daysinmon[12] =  {31,28,31,30,31,30,31,31,30,31,30,31};
static ub4 daysinmon2[12] = {31,29,31,30,31,30,31,31,30,31,30,31};
static ub4 *yymm2daytab;
static ub4 *day2cdtab;
static ub4 day2cdmax;
static ub4 yymmtablen;
static ub4 epochday,eraday;

static const ub4 maxtmosec = 60;

void initime(int iter)
{
  char buf[256];
  ub4 now;
  ub4 years,months,days,yy,mm,dd,d;

  msgfile = setmsgfile(__FILE__);
  iniassert();

  int vrb = (globs.prog == Progto || globs.prog == Progvisv);

  // create calendar dates to minute table, supporting typically 10 years around now
  // mktime() is hardly useful as it refers to a fixed system TZ.
  if (iter == 0) {
    years = Erayear - Epochyear;
    months = years * 12;
    yymmtablen = months;
    days = 0;
    yymm2daytab = alloc(months,ub4,0,"misc",0);
    day2cdtab = alloc(months * 31,ub4,0,"misc",0);
    day2cdmax = months * 31 - 1;

    for (yy = 0; yy < years; yy++) {
      for (mm = 0; mm < 12; mm++) {
        dd = (yy % 4) ? daysinmon[mm] : daysinmon2[mm];
        yymm2daytab[yy * 12 + mm] = days;
        for (d = 0; d < dd; d++) day2cdtab[days+d] = (yy + Epochyear) * 10000 + (mm + 1) * 100 + d + 1;
        days += dd;
      }
    }

    epochday = cd2day(Epoch);
    eraday = cd2day(Era1);

  } else {
    now = (ub4)time(NULL);
    sec70toyymmdd(now,12,buf,sizeof(buf));
    infovrb(vrb,Emp,"current time %s utc",buf);
  }

}

void exitime(void)
{
  afree(yymm2daytab,"misc");
  afree(day2cdtab,"misc");
}

// add utcofs: utc to local
ub4 min2lmin(ub4 min,ub4 utcofs)
{
  if (min <= utcofs) { warning(0,"time %u for utc offset %u before Epoch UTC",min,utcofs); return min; }
  else if (utcofs < 12 * 60) return min - (12 * 60 - utcofs);
  else if (utcofs > 12 * 60) return min + (utcofs - 12 * 60);
  else return min;
}

// idem, support local time
ub4 min2llmin(ub4 min,ub4 utcofs,ub4 locofs,ub4 dstonof)
{
  if (utcofs >= 26 * 60) utcofs = locofs;
  else dstonof = 0;
  if (utcofs >= 26 * 60) return min;
  // info(0,"utc \ad%u ofs %u",min,utcofs);
  if (min <= utcofs) { warning(0,"time %u for utc offset %u before Epoch UTC",min,utcofs); return min; }
  else if (utcofs < 12 * 60) min -= (12 * 60 - utcofs);
  else if (utcofs > 12 * 60) min += (utcofs - 12 * 60);
  if (dstonof == 0) return min;
  ub4 day = min / 1440;
  if (indst(day,dstonof)) min += 60;
  return min;
}

// sub utcofs
ub4 lmin2minfln(ub4 fln,ub4 lmin,ub4 utcofs)
{
  if (lmin < utcofs) {
    warnfln2(fln,0,FLN,"time %u at utc offset %u before Epoch UTC",lmin,utcofs);
    return lmin;
  } else if (lmin == utcofs) return 0;
  else if (utcofs < 12 * 60) return lmin + (12 * 60 - utcofs);
  else if (utcofs > 12 * 60) return lmin - (utcofs - 12 * 60);
  else return lmin;
}

// coded decimal to biased
ub4 utc12ofs(ub4 uo12)
{
  ub4 hh,mm;

  hh = uo12 / 100; mm = uo12 % 100;
  return hh * 60 + mm;
}

ub4 sec70toyymmdd(ub4 secs,ub4 prec,char *dst,ub4 dstlen)
{
  time_t t = (time_t)secs;
  struct tm *tp = gmtime(&t);
  ub4 pos = mysnprintf(dst,0,dstlen,"%04u-%02u-%02u %02u:%02u",tp->tm_year+1900,tp->tm_mon+1,tp->tm_mday,tp->tm_hour,tp->tm_min);
  if (prec > 10) pos += mysnprintf(dst,pos,dstlen,":%02u",tp->tm_sec);
  return pos;
}

// minutes since epoch localtime to decimal-coded 20140522
ub4 lmin2cd(ub4 min)
{
  ub4 day;
  ub4 pos;
  char buf[1024];

  day = min / 1440;
  if (day >= day2cdmax) {
    pos = fmtstring(buf,"W day %u after Epoch %u : %u\n",day,Erayear,day2cdmax);
    msg_write(buf,pos);
  }
  if (day2cdtab) return day2cdtab[min(day,day2cdmax)];
  pos = fmtstring(buf,"E time module not inited for min %u\n",min);
  msg_write(buf,pos);
  return 0;
}

// day to coded decimal yyyymmdd
ub4 day2cdfln(ub4 fln,ub4 day)
{
  ub4 pos;
  char buf[256];

  if (day >= day2cdmax) {
    pos = fmtstring(buf,"day2cd: day %u after Epoch %u: %u",day,Erayear,day2cdmax);
    msg_errwrite(fln,FLN,0,buf);
    day = day2cdmax;
  }
  return day2cdtab[day];
}

// coded decimal day to day, tz-agnostic
ub4 cd2dayfln(ub4 fln,ub4 orgcd)
{
  ub4 d,m,y,mm,yy,dm,day,ndx,cd = orgcd;
  ub4 pos;
  char buf[1024];
  char flnbuf[256];

  msgfln(flnbuf,0,sizeof(flnbuf),fln,0);

  d = cd % 100;
  if (d == 0) { pos = fmtstring(buf,"W %s cd2day day in %u zero\n",flnbuf,cd); msg_write(buf,pos); d = 1; }
  else if (d > 31) { pos = fmtstring(buf,"W %s cd2day day %u above 31\n",flnbuf,d); msg_write(buf,pos); d = 31; }
  cd /= 100;
  m = cd % 100;
  if (m == 0) { pos = fmtstring(buf,"W %s cd2day month in %u zero\n",flnbuf,orgcd); msg_write(buf,pos); m = 1; }
  else if (m > 12) { pos = fmtstring(buf,"W %s cd2day month %u above 12\n",flnbuf,m); msg_write(buf,pos); m = 12; }
  dm = daysinmon2[m-1];
  if (d > dm) { pos = fmtstring(buf,"W %s cd2day invalid day %u in month %u\n",flnbuf,d,m); msg_write(buf,pos); d = dm; }

  y = cd / 100;
  if (y < Epochyear) {
    pos = fmtstring(buf,"W %s cd2day %u: year %u before lowest supported %u\n",flnbuf,orgcd,y,Epochyear);
    msg_write(buf,pos);
    y = Epochyear;
  } else if (y >= Erayear) {
    pos = fmtstring(buf,"W %s cd2day %u: year %u after highest supported %u\n",flnbuf,orgcd,y,Erayear-1);
    msg_write(buf,pos);
    y = Erayear - 1; m = 12; d = 31;
  }

  yy = y - Epochyear;
  mm = m - 1;
  ndx = yy * 12 + mm;
  error_ge_cc(ndx,yymmtablen,"year %u mon %u",y,m);
  day = yymm2daytab[ndx] + (d - 1);
  return day;
}

int epochrange(ub4 fln,ub4 cd,const char *name)
{
  if (cd < Epoch) return errorfln(FLN,0,fln,"var %s %u below epoch %u",name,cd,Epoch);
  else if (cd >= Era) return errorfln(FLN,0,fln,"var %s %u above era %u",name,cd,Era);
  else return 0;
}

ub4 epochlim(ub4 day)
{
  day = min(day,eraday);
  day = max(day,epochday);
  return day;
}

// 20140226 localtime to minutes utc since epoch
ub4 yymmdd2min(ub4 cd,ub4 utcofs)
{
  ub4 days;
  ub4 lmin;

  days = cd2day(cd);
  lmin = days * 1440;
  return lmin2min(lmin,utcofs);
}

// coded decimal day to weekday, tz-agnostic
ub4 cdday2wday(ub4 cd)
{
  ub4 day = cd2day(cd);
  ub4 wday = (day + Epochwday) % 7;
  return wday;
}

// weekday of minute time
ub4 min2wday(ub4 min)
{
  ub4 day = min / 1440;
  ub4 wday = (day + Epochwday) % 7;
  return wday;
}

// coded decimal 1230 to minutes
ub4 hhmm2min(ub4 ct)
{
  ub4 h = ct / 100;
  ub4 m = ct % 100;
  return h * 60 + m;
}

// t in dst active
ub1 indst(ub4 t,ub4 dstonof)
{
  if (dstonof == 0) return 1;

  ub4 dstof = dstonof % 10000;
  ub4 dston = dstonof / 10000;

  if (dston == 0 || dstof == 0) return 0;

  ub4 tmmdd = day2cd(t) % 10000;
  if (dston < dstof) {
    if (tmmdd >= dston && tmmdd < dstof) return 1;
  } else {
    if (tmmdd < dstof || tmmdd >= dston) return 1;
  }
  return 0;
}

ub4 gettime_sec(void)
{
  ub8 usec = gettime_usec();
  return (ub4)(usec / (1000 * 1000));
}

ub8 gettime_msec(void)
{
  ub8 usec = gettime_usec();
  return usec / 1000;
}

ub8 thrtime_usec(void)
{
  ub8 usec;

  int rv = osclock_gettime(&usec);
  if (rv) return 0;

  return usec;
}

int setimer(ub4 msec,bool virtual)
{
  if (msec > 1000 * maxtmosec) {
    warn(Emp,"timeout limited from %u to %u sec",msec / 1000,maxtmosec);
    msec = 1000 * maxtmosec;
  }
  return ostimer(msec,virtual);
}

int setthtimer(ub4 tid,ub4 msec)
{
  return osthtimer(tid,msec);
}

int rmthtimer(ub4 tid)
{
  return osrmthtimer(tid);
}

int isexpired(ub4 tid)
{
  return osisexpired(tid);
}

int isalarm(void)
{
  return osisalarm();
}

ub4 nix2min(ub4 xmin)
{
  ub4 days = (Epochyear - 1970) * 365 + 7;
  ub4 min,day;
  if (days * 1440 > xmin) return warn(0,"unix minute time %u before Epoch %u",xmin,Epochyear);
  min = xmin - (days * 1440);
  day = min / 1440;
  if (day >= day2cdmax) {
    warn(0,"unix minute time %u after Era %u : day %u after %u",xmin,Erayear,day,day2cdmax);
    return (day2cdmax - 1) * 1440;
  }
  return min;
}
