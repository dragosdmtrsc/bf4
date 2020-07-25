from csv import reader
import sys
import os
import time
import subprocess
import sys
from subprocess import DEVNULL

if len(sys.argv) < 2:
    print('usage: python3 {} <out dir>'.format(sys.argv[0]))
    sys.exit(-1)
fin = sys.stdin
outdir = sys.argv[1]

def version(prog):
    try:
        subprocess.check_call(['p4test', '--parse-only', prog], stderr=DEVNULL, stdout=DEVNULL)
        return 16
    except:
        try:
            subprocess.check_call(['p4test', '--parse-only', '--std', 'p4-14', prog], stderr=DEVNULL, stdout=DEVNULL)
            return 14
        except:
            return 0

for l in reader(fin):
    if len(l) < 2:
        print('expecting <file>,v1')
        continue
    file = os.path.abspath(l[0])
    ver = version(file)
    if ver == 0:
        print('can\'t tell version for {}'.format(file))
        continue
    p = os.path.basename(file)
    p=os.path.splitext(p)[0]
    inkind = l[1]
    dname = '{}_{}'.format(p, inkind)
    dname = os.path.join(outdir, dname)
    if not os.path.exists(dname):
        os.makedirs(dname)
    arglist=['p4c-bm2-ss']
    print('{} version {}'.format(p, ver))
    if ver == 14:
        arglist.extend(['--std', 'p4-14'])
    arglist.extend(['--make-field-lists', '{}-with-fieldlists.p4'.format(p)])
    arglist.append(file)
    cleanlog=open(os.path.join(dname, 'cleanup_log.txt'), 'w')
    try:
        subprocess.check_call(arglist, cwd=dname, stderr = cleanlog, stdout = cleanlog)
    except:
        print('failed to cleanup for {}'.format(p))
        continue
    finally:
        cleanlog.close()
    kwork = os.path.abspath(os.path.join('.', 'kitchen_work.sh'))
    v1int = os.path.abspath(os.path.join('v1_integration.p4'))
    arglist = [kwork, '{}-with-fieldlists.p4'.format(p), v1int, '.']
    kitchenlog=open(os.path.join(dname, 'kitchen_log.txt'), 'w')
    try:
        subprocess.check_call(arglist, cwd=dname, stderr = kitchenlog, stdout = kitchenlog)
    except:
        print('failed to do kitchen work for {}'.format(p))
        continue
    print('ok for {}'.format(p))