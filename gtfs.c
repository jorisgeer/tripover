// gtfs.c - gtfs support

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2015 Joris van der Geer.
 */

/* Write gtfs files from processed tripover input.

  Tripover does not read gtfs files directly. Instead, gtfstool converts them.
  Export to gtfs allows operations like timezone conversion.
  This is needed for combining feeds.
 */

#include <string.h>
#include <stdarg.h>

#include "base.h"
#include "cfg.h"
#include "mem.h"
#include "math.h"

static ub4 msgfile;
#include "msg.h"

#include "time.h"
#include "util.h"
#include "netbase.h"
#include "netio.h"
#include "event.h"
#include "gtfs.h"

static double lat2gt(ub4 lat,ub4 scale) { return ((double)lat / scale) - 90; }
static double lon2gt(ub4 lon,ub4 scale) { return ((double)lon / scale) - 180; }

int writegtfs(struct networkbase *net,char *outdir)
{
  struct portbase *ports,*pp;
  struct routebase *rp,*routes;
  struct subportbase *spp,*sports;
  struct chainbase *cp,*chains;

  ub4 portcnt,routecnt,chaincnt;
  ub4 port,sport,route,chain;
  ub4 id,pid,rid,tid,sid;
  double x,y;
  ub4 scnt,sofs;
  char *uid;
  char fname[1024];
  char buf[1024];
  ub4 pos;
  int fd;

  portcnt = net->portcnt;
  ports = net->ports;
  sports = net->subports;
  routes = net->routes;
  routecnt = net->ridcnt;
  chains = net->chains;
  chaincnt = net->rawchaincnt;

  uid = outdir;

  fmtstring(fname,"%s/stops.txt",outdir);

  info(0,"writing %s",fname);
  fd = filecreate(fname,1);
  if (fd == -1) return 1;

  pos = fmtstring0(buf,"stop_id,location_type,parent_station,stop_name,stop_lat,stop_lon,stop_desc\n");
  if (filewrite(fd,buf,pos,fname)) return 1;

  for (port = 0; port < portcnt; port++) {
    pp = ports + port;
    if (pp->ndep == 0 && pp->narr == 0) continue;

    scnt = pp->subcnt;
    sofs = pp->subofs;

    y = lat2gt(pp->lat,net->latscale);
    x = lon2gt(pp->lon,net->lonscale);

    if (scnt == 0) {
      id = port;
      pos = fmtstring(buf,"%s%u,0,,\a`%s,%f,%f,%u\n",uid,id,pp->name,y,x,pp->id);
      if (filewrite(fd,buf,pos,fname)) return 1;
      continue;
    }

    pid = port;
    pos = fmtstring(buf,"%s%u,1,,\a`%s,%f,%f,%u\n",uid,pid,pp->name,y,x,pp->id);
    if (filewrite(fd,buf,pos,fname)) return 1;
    for (sport = 0; sport < scnt; sport++) {
      spp = sports + sofs + sport;
      y = lat2gt(spp->lat,net->latscale);
      x = lon2gt(spp->lon,net->lonscale);
      id = spp->subid + portcnt;
      pos = fmtstring(buf,"%s%u,0,%s%u,\a`%s,%f,%f,%u\n",uid,id,uid,pid,spp->name,y,x,spp->id);
      if (filewrite(fd,buf,pos,fname)) return 1;
    }
  }
  fileclose(fd,fname);
  info(0,"wrote %s",fname);

  fmtstring(fname,"%s/routes.txt",outdir);

  info(0,"writing %s",fname);
  fd = filecreate(fname,1);
  if (fd == -1) return 1;

  pos = fmtstring0(buf,"route_id,agency_id,route_short_name,route_long_name,route_type\n");
  if (filewrite(fd,buf,pos,fname)) return 1;

  for (route = 0; route < routecnt; route++) {
    rp = routes + route;
    pos = fmtstring(buf,"%s%u,,,\a`%s,%u\n",uid,route,rp->name,rp->rtype);
    if (filewrite(fd,buf,pos,fname)) return 1;
  }

  fileclose(fd,fname);
  info(0,"wrote %s",fname);

  fmtstring(fname,"%s/trips.txt",outdir);

  info(0,"writing %s",fname);
  fd = filecreate(fname,1);
  if (fd == -1) return 1;

  pos = fmtstring0(buf,"route_id,service_id,trip_id,trip_headsign\n");
  if (filewrite(fd,buf,pos,fname)) return 1;

  for (chain = 0; chain < chaincnt; chain++) {
    cp = chains + chain;
    rid = cp->rid;
    tid = chain;
    sid = 0;
    pos = fmtstring(buf,"%s%u,%s%u,%s%u,\a`%s\n",uid,rid,uid,sid,uid,tid,"");
    if (filewrite(fd,buf,pos,fname)) return 1;
  }

  fileclose(fd,fname);
  info(0,"wrote %s",fname);

  return 0;
}

int inigtfs(void)
{
  msgfile = setmsgfile(__FILE__);
  iniassert();
  return 0;
}
