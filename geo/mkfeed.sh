#!/bin/sh

wget http://download.geonames.org/export/dump/allCountries.zip

unzip allCountries.zip

cat headline allCountries.txt > all.tab
