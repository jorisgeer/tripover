#!/bin/bash

# This file is part of Tripover, a broad-search journey planner.

# Copyright (C) 2015-2016 Joris van der Geer.

# example script to setup development environment
# last changed 1 Jan 2016

set -eu

# Adapt to your needs

# Estimate walk and taxi modes using road network. Optional
# Select a file that covers the intended area
load_osm=yes
osmserver=http://download.geofabrik.de
osmfile=australia-oceania-latest.osm.pbf

# Support localtime display. Optional
load_geonames=yes

function error_exit()
{
  local msg=${1-'n/a'}

  echo "error: $msg" && exit 1
}

[[ -f tripover.c ]] || error_exit "run this script as ./setup.sh"
[[ -f emka ]] || error_exit "run this script as ./setup.sh"

./emka config || error_exit "emka config failed"

echo "building ..."
./emka -u || error_exit "emka failed"
echo "build done"

./tripover init

[[ -d rep ]] || mkdir rep
[[ -d queries ]] || mkdir queries

[[ -d geo ]] || mkdir geo
cd geo

[[ "$load_geonames" = "yes" ]] || touch all.tab

if [ ! -f all.tab ]; then
  echo "downloading geonames (300 MB)"
  wget http://download.geonames.org/export/dump/allCountries.zip
  echo -e "id\tname\tascname\taltname\tlat\tlon\tclass\tfcode\tcc\tcc2\tadm1\tadm2\tadm3\tadm4\tpop\tzdem\ttz\tmtime" > headline
  unzip allCountries
  cat headline allCountries.txt > all.tab
  rm allCountries.txt
fi
cd ..

[[ -d osm ]] || mkdir osm
orgdir=$PWD
cd osm

if [ ! -f osmconvert ]; then
  wget -nv http://m.m.i24.cc/osmconvert.c
  gcc -O3 -o osmconvert osmconvert.c -lz
fi

if [ "$load_osm" = "yes" ]; then
  if [ ! -f $osmfile ]; then
    echo "downloading $osmfile. This may take a while"
    wget "$osmserver/$osmfile"
  fi
  echo "converting $osmfile"
  ./osmconvert -v --drop-author --drop-version -o=au.o5m $osmfile
  echo "processing $osmfile"
  cd ..
  osmprep osm osm/au.o5m
fi
cd $orgdir

[[ -f feeds.cfg ]] || cp -n example-feeds.cfg feeds.cfg
[[ -f feedscripts.tar ]] && tar xf feedscripts.tar

echo "setup done, you can now configure feeds:"
echo "adapt feeds.cfg"
echo "./mkfeed.pl"
echo ""
echo "adapt tripover.cfg"
echo "./tripover run feeds"
