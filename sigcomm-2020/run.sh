#!/bin/bash

if [[ $# -lt 1 ]];
then
echo "$0 <p4file>"
exit 1;
fi

cleanup=1
if [[ $# -ge 2 ]];
then
    if [[ $2 -eq "-noclean" ]];
    then
        cleanup=0
    fi
fi

fname=$(basename $1)
dname=$(dirname $1)
fixed="$fname.fixed.p4"
beforefix="$fname.fixed.p4.orig"
inferred="$fname.inferred.txt"
instrumented="$fname.instrumented.p4"
logfile="$fname.log.txt"
infer="$fname.inferlog.txt"
echo "running..."
/usr/bin/time -v p4c-analysis -T cegis.cpp:4 \
-T infer.cpp:4 \
--infer $inferred \
--fixes $fixed \
--revive-packet \
--dump-instrumented $instrumented \
$1 &> $logfile
mv infer.txt $infer
archive="$fname.run.tgz"
echo "archiving..."
tar -cvzf $archive $infer $fixed $beforefix $logfile $instrumented $inferred -C $dname $fname
if [[ $cleanup -eq 1 ]];
then
    echo "cleaning..."
    rm -f $infer $fixed $beforefix $logfile $inferred $instrumented
fi