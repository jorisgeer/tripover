#!/bin/bash

set -eux

error_exit()
{
  echo $*
  exit 1
}

totext()
{
  [[ $# -lt 1 ]] && error_exit 'missing arguments'

  local pdf="$1"

  local txt
  local ltxt
  local rtxt
  local period
  local loadtime

# left
  txt="${pdf/%\.pdf/.txt}"
  ltxt="${pdf/%\.pdf/_l.txt}"
  pdftotext -x 0 -y 0 -W 295 -H 900 -f 5 -layout "$pdf" || error_exit "cannot convert"
  mv "$txt" "$ltxt"

 # right
  txt="${pdf/%\.pdf/.txt}"
  rtxt="${pdf/%\.pdf/_r.txt}"
  pdftotext -x 295 -y 0 -W 295 -H 900 -f 5 -layout "$pdf" || error_exit "cannot convert"
  mv "$txt" "$rtxt"

  pdftotext -l 1 "$pdf"

  period=$(fgrep period "$txt")
  loadtime=$(date -R)
  echo "period $period" > period
  echo "loadtime $loadtime" > loadtime

  cat period loadtime "$ltxt" "$rtxt" > timetable-raw.txt
}

[[ $# -lt 1 ]] && error_exit 'missing arguments'

cd ..

[[ -d sky ]] || mkdir sky
cd sky

[[ -d in ]] || mkdir in

cd in

pdf=Skyteam_Timetable.pdf
[[ -f $pdf ]] && mv $pdf $pdf.bak

wget "$1" || error_exit "cannot download $pdf"

totext $pdf || exit 1
