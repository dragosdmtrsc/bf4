#/bin/bash

grep -R -e "prepare time" -e "total time" -e "instrumentation time" -e "uncontrolled count"  *.log.* | \
 sed -e "s/\(.*\.p4\)\.log\.\([a-z]\+\)\.txt\(.*\)/\1,\2,\3/" | \
 sed 's/ms//' | \
 sed 's/\(.*\) \([0-9]\+\)/\1,\2/' > stats.csv

grep -R -e "no control"  *.log.* | sed -e "s/\(.*\.p4\)\.log\.\([a-z]\+\)\.txt:no control over.*/\1,\2,nocontrol,1/" >> stats.csv
grep -R -e "#bugs"  *.log.* | sed -e "s/\(.*\.p4\)\.log\.\([a-z]\+\)\.txt:#bugs:\([0-9]\+\)/\1,\2,#bugs,\3/"  >> stats.csv
grep -R -e "fix in"  *.log.* | sed -e "s/\(.*\.p4\)\.log\.\([a-z]\+\)\.txt:fix in \(.*\)/\1,\2,fix,1,\3/" >> stats.csv

grep -R -e "fix in"  *.log.* | sort | grep -o ".*fix in [^ ]\+ table [^\ ]\+" | \
 uniq | sed -e "s/\(.*\.p4\)\.log\.\([a-z]\+\)\.txt:fix in \(.*\)/\1,\2,table_fixes,1,\3/" >> stats.csv

grep -H "table_stats" *log.infer*  | \
sed -e "s/\(.*\.p4\)\.log\.\([a-z]\+\)\.txt:table_stats,[^,]\+.*/\1/" | \
sort | \
uniq -c | \
sort -n | \
sed 's/[ ]*\([0-9]\+\) \(.*\)/\2,infer,#Tables,\1/' >> stats.csv

grep -H "table_stats" *log.infer*  | \
sed -e "s/\(.*\.p4\)\.log\.\([a-z]\+\)\.txt:table_stats,.*,\([0-9]\+\),.*/\1,infer,#Keys,\3/" >> stats.csv

sed -i 's/:instrumentation time/Instrumentation (s)/' stats.csv
sed -i 's/fixes,fix/fixes,#Fixes/' stats.csv
sed -i 's/table_fixes/#Table fixes/' stats.csv
sed -i 's/:uncontrolled count time/Find uncontrolled (s)/' stats.csv
sed -i 's/:prepare time/Prepare (s)/' stats.csv
sed -i 's/:total time/Total (s)/' stats.csv
sed -i 's/nocontrol/#Uncontrolled/' stats.csv
