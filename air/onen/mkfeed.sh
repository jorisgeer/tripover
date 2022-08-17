#!/bin/bash

set -eu

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
  pdftotext -x 0 -y 0 -W 260 -H 900 -f 7 -layout "$pdf" || error_exit "cannot convert"
  mv "$txt" "$ltxt"

 # right
  txt="${pdf/%\.pdf/.txt}"
  rtxt="${pdf/%\.pdf/_r.txt}"
  pdftotext -x 260 -y 0 -W 270 -H 900 -f 7 -layout "$pdf" || error_exit "cannot convert"
  mv "$txt" "$rtxt"

  pdftotext -l 1 "$pdf" || error_exit "cannot convert"
  period=$(fgrep Valid "$txt")
  loadtime=$(date -R)
  echo "period $period" > period
  echo "loadtime $loadtime" > loadtime

  cat period
  cat period loadtime "$ltxt" "$rtxt" > timetable-raw.txt
}

[[ $# -lt 1 ]] && error_exit 'missing arguments'

cd ..

[[ -d one ]] || mkdir one
cd one

[[ -d in ]] || mkdir in

cd in

pdf=oneworld.pdf
[[ -f $pdf ]] && mv $pdf $pdf.bak

wget "$1" || error_exit "cannot download $pdf"

totext $pdf || exit 1
