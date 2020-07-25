#!/bin/bash
set -e
set -o xtrace
if [[ $# -lt 2 ]];
then
    echo "usage: ./kitchen_work.sh p4 template [outdir]"
    exit 1
fi

if [[ ! -f $1 ]];
then
    echo "no such file $1"
    exit 1
fi

if [[ ! -f $2 ]];
then
    echo "template doesn't exist"
fi

fname=$1
template=$2
outdir=${3:-.}

if [[ ! -d $outdir ]];
then
    echo "directory $outdir not there"
    exit 1
fi

trimmed=`basename $fname .p4`
time p4c-analysis --dump-instrumented "${outdir}/${trimmed}-instrumented.p4" ${fname}
echo "instrumented ${outdir}/${trimmed}-instrumented.p4"
time p4c-analysis --expand-to "${outdir}/${trimmed}-instrumented-expanded.p4" "${outdir}/${trimmed}-instrumented.p4"
echo "expanded ${outdir}/${trimmed}-instrumented-expanded.p4"
time p4c-analysis --render-integration "${outdir}/${trimmed}-integrated.p4" \
 --integration-template ${template} --render-only "${outdir}/${trimmed}-instrumented-expanded.p4"
echo "integrated ${outdir}/${trimmed}-integrated.p4"