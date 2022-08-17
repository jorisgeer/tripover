#!/bin/bash

set -eux

error_exit()
{
  echo $*
  exit 1
}

[[ $# -lt 1 ]] && error_exit 'missing arguments'

cd ..

[[ -f in/$1 ]] || error_exit "in/$1 not found"

unzip -o in/$1 || error_exit "cannot unpack $1"

for i in 1 2 3 4 5 6 7 8 10 11; do
  [[ -d $i/in ]] || mkdir -p $i/in
  mv $i/google_transit.zip $i/in;
done
