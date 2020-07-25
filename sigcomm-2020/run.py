
import sys
import os
import argparse
import subprocess
import time
import sys

parser = argparse.ArgumentParser(description='Process p4 files')
parser.add_argument('p4s', nargs='+',
                    help='p4 files to analyze')
parser.add_argument('--stat-folder', default='.', dest='stat')
parser.add_argument('--infer', default='both', dest='infer', choices=['both', 'fixes', 'infer'])
parser.add_argument('--no-egress-spec', dest = 'egress_spec', action='store_false')
parser.add_argument('--optimize', dest = 'optimized', action='store_true')


#grep -R -e "prepare time" -e "total time" -e "instrumentation time" -e "uncontrolled count"  *.log.* |
# sed -e "s/\(.*\.p4\)\.log\.\([a-z]\+\)\.txt\(.*\)/\1,\2,\3/" |
# sed 's/ms//' |
# sed 's/\(.*\) \([0-9]\+\)/\1,\2/' > stats.csv

#grep -R -e "no control"  *.log.* | sed -e "s/\(.*\.p4\)\.log\.\([a-z]\+\)\.txt:no control over.*/\1,\2,nocontrol,1/" >> stats.csv
#grep -R -e "#bugs"  *.log.* | sed -e "s/\(.*\.p4\)\.log\.\([a-z]\+\)\.txt:#bugs:\([0-9]\+\)/\1,\2,#bugs,\3/"  >> stats.csv
#grep -R -e "fix in"  *.log.* | sed -e "s/\(.*\.p4\)\.log\.\([a-z]\+\)\.txt:fix in \(.*\)/\1,\2,fix,1,\3/" >> stats.csv

#grep -R -e "fix in"  *.log.* | sort | grep -o ".*fix in [^ ]\+ table [^\ ]\+" |
# uniq | sed -e "s/\(.*\.p4\)\.log\.\([a-z]\+\)\.txt:fix in \(.*\)/\1,\2,fix,1,\3/" >> stats.csv
args = parser.parse_args()
if not os.path.isdir(args.stat):
    os.mkdir(args.stat)
if args.infer == 'both':
    choices=['infer', 'fixes']
elif args.infer == 'fixes':
    choices=['fixes']
else:
    choices=['infer']
for f in args.p4s:
    p = os.path.basename(f)
    instrumented = '{0}.instrumented.p4'.format(p)
    instrumented = os.path.join(args.stat, instrumented)
    options = []
    options.append('-T')
    options.append('infer.cpp:4')
    options.append('-T')
    options.append('analysis.cpp:4')
    options.append('--dump-instrumented')
    options.append(instrumented)
    options.append('--without-ifs')
    for choice in choices:
        print ("running " + p + " choice " + choice)
        inferf = '{0}.inferred.{1}.txt'.format(p, choice)
        inferf = os.path.join(args.stat, inferf)
        fixf = '{0}.fixed.p4'.format(p)
        fixf = os.path.join(args.stat, fixf)
        coptions = list(options)
        coptions.append('--infer')
        coptions.append(inferf)
        if choice == 'fixes':
            coptions.append('--fixes')
            coptions.append(fixf)
        coptions.append(f)
        if args.egress_spec:
            coptions.append('--revive-packet')
        if args.optimized:
            coptions.append('--optimize')
        logfile = '{0}.log.{1}.txt'.format(p, choice)
        logfile = os.path.join(args.stat, logfile)
        my_cmd = ['p4c-analysis'] + coptions
        ret = 0
        elapsed=0.0
        for i in range(3):
            with open(logfile, "w") as outfile:
                start = time.time()
                ret=subprocess.call(my_cmd, stdout=outfile, stderr=outfile)
                end = time.time()
                elapsed=end-start
                if ret == 0:
                    break
        if ret != 0:
            print("can't execute command for " + p + " choice " + choice)
        else:
            print('succesfully ran ' + p + ' choice ' + choice + ' in ' + str(elapsed) + 's')