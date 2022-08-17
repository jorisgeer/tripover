#!/bin/bash

set -exu

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
  local period
  local loadtime

  txt="${pdf/%\.pdf/.txt}"

  pdftotext -raw -f 5 -l 5 "$pdf" || error_exit "cannot convert"
  period=$(fgrep between "$txt")

  pdftotext -raw -f 5 "$pdf" || error_exit "cannot convert"

  loadtime=$(date -R)
  echo "period $period" > period
  echo "loadtime $loadtime" > loadtime

  cat period loadtime "$txt" > timetable-raw.txt
}

[[ $# -lt 1 ]] && error_exit 'missing arguments'

echo $PWD

cd ..

[[ -d qantas ]] || mkdir qantas
cd qantas

[[ -d in ]] || mkdir in

cd in

pdf=qf_pdfTimetable.pdf
[[ -f $pdf ]] && mv $pdf $pdf.bak

echo $PWD
wget "$1" || error_exit "cannot download $pdf"

totext $pdf || exit 1

exit 0
