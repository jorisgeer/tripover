// gtfs.h - gtfs support

/* Write gtfs files from processed tripover input.

  Tripover does not read gtfs files directly. Instead, gtfstool converts them.
  Export to gtfs allows operations like timezone conversion.
  This is needed for combining feeds.
 */

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2015 Joris van der Geer.
 */

extern int inigtfs(void);
extern int writegtfs(struct networkbase *net,char *outdir);
