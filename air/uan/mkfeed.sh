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

  txt="${pdf/%\.pdf/.txt}"
  pdftotext -f 1 -l 1 -raw "$pdf" || error_exit "cannot convert"
  period=$(tail -n 3 "$txt" | fgrep ' to ')
  cp "$txt" period.tmp
  pdftotext -f 107 -raw "$pdf" || error_exit "cannot convert"
  sed -i -e 's/Ã¢â‚¬â€œ//' "$txt"
  loadtime=$(date -R)
  echo "period $period" > period
  echo "loadtime $loadtime" > loadtime

  cat period loadtime "$txt" > timetable-raw.txt
}

[[ $# -lt 1 ]] && error_exit 'missing arguments'

cd ..

[[ -d ua ]] || mkdir ua
cd ua

[[ -d in ]] || mkdir in

cd in

pdf=united.pdf
[[ -f $pdf ]] && mv $pdf $pdf.bak

# wget "$1" || error_exit "cannot download $pdf"
cp -p timetable.pdf $pdf || error_exit "cannot download $pdf"

totext $pdf || exit 1
