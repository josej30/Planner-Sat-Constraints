#! /usr/bin/env python2.5
# -*- coding: latin-1 -*-

import sys
import os
import parsepddl
import re
import subprocess
import marshal
import pddlsfromtar
import timeout

Loc='/home/hlp/work/memory-less-blai-2009'

def usage():
    print """
Usage: %s {-mo} {-z} {-d} {-c} {-l} <domain> <problem>'
mo = mutex obs and states
z = only zoom mutex
d = debug
c = compile and finish
l = use LAMA instead of SATPLAN
"""
    sys.exit(1)

if len(sys.argv) < 2:
    usage()

mutex_obs = False
only_zoom = False
debug=False
just_compile = False
use_lama = False

for i in sys.argv:
    print i,
print

t=int(60*60*1.5)
i = 1
while i < len(sys.argv):
    if sys.argv[i] == '-mo':
        mutex_obs = True
    elif sys.argv[i] == '-z':
        only_zoom = True
    elif sys.argv[i] == '-d':
        debug = True
    elif sys.argv[i] == '-c':
        just_compile = True
    elif sys.argv[i] == '-l':
        use_lama = True
    elif sys.argv[i] == '-t':
        i += 1
        t = int(sys.argv[i])
        print 'Using limit in seconds:',t
    else:
        break
    i += 1

[has_tar,domain_nf,problem_nf] = pddlsfromtar.get_pddls(sys.argv[i])
if i + 1 == len(sys.argv) and has_tar:
    pass
elif i + 2 > len(sys.argv):
    usage()
else:
    domain_nf=sys.argv[i]
    problem_nf=sys.argv[i+1]

#debug=True
debug2=debug
if debug:
    print sys.argv

predicates=parsepddl.get_predicates(domain_nf)
if debug:
    print predicates

# Obtaining observations and q-states
obs=[]
states=[]
for p in predicates:
    p = p[0]
    if p.startswith('OBS'):
        obs.append(p.split('OBS')[1])
    elif re.match('Q[0-9]+',p):
        states.append(p)
if debug:
    print 'OBS:',obs
    print 'STATES:',states

# Creating observations.txt
obs_file = file('observations.txt','w')
obs_token=set({})
print >>obs_file, len(obs)*len(states)
for o in obs:
    for q in states:
        # WATCH OUT: observation,state format in action names
        token = '-'+o+'-'+q+'-'
        print >>obs_file, token
        obs_token.add(token)
print >>obs_file
obs_file.close()

# Calling cf2cs
if use_lama:
    rescmd = ['-fs0','-s','new',domain_nf,problem_nf]
else:
    rescmd = ['-fs0','-pln','-s','new',domain_nf,problem_nf]

try:
    cmd=[Loc+'/cf2cs']
    cmd.extend(rescmd)
    cf2cs=subprocess.Popen(cmd,bufsize=1000, stdout=subprocess.PIPE)
except:
    cmd=[os.getcwd()+'/cf2cs']
    cmd.extend(rescmd)
    cf2cs=subprocess.Popen(cmd,bufsize=1000, stdout=subprocess.PIPE)

loading_table = False

# will contain translation table from short to long predicates
short2long={}
long2short={}
for l in cf2cs.stdout.readlines():
    print l,
    if l.startswith('Short to Long atoms translation'):
        loading_table = True
    elif l.startswith('===============================') and \
         len(short2long) <> 0:
        loading_table = False
    elif loading_table and '->' in l:
        l = l.upper().split('->')
        short = l[0].strip()
        long = l[1].strip()
        short2long[short] = long
        long2short[long] = short

res = cf2cs.wait()
if(res < 0):
    pr('Error calling cf2cs: %d ' % res)
    sys.exit(1)

sys.stdout.flush()

if just_compile:
    sys.exit(0)

if not use_lama:
    # Prepare satplan
    if debug and False:
        print short2long

    # Calculating tags
    tags=set({})
    for p in long2short:
        if '__' in p:
            tags.add(p.split('__')[1][:-1])

    if debug:
        print tags

    # Loading predicates of classical PDDL
    predicates_new=parsepddl.get_predicates('new-d.pddl')
    if debug:
        print predicates_new

    save=[mutex_obs,obs,states,obs_token,tags,short2long,long2short]
    marshal.dump(save,file('memory-less.dat','w'))

    if only_zoom:
        zoom='-a ZOOM'
    else:
        zoom=''

def run_num2sat(l):
    cmd = l+'/num2sat '+zoom+' -s 2 -o new-d.pddl -f new-p.pddl -m observations.txt'
    cmd = cmd.split()
    num2sat=subprocess.Popen(cmd,bufsize=1000)
    res = num2sat.wait()

def run_lama(l):
    cmd = l+'/lama/plan new-d.pddl new-p.pddl res.lama'
    print 'CMD =', cmd
    cmd = cmd.split()
    lama=subprocess.Popen(cmd,bufsize=1000)
    res = lama.wait()
    
def run_timed(runit,l):
    global t
    try:
        timeout.TimedOutFn(runit, t, l)
        return "Finished"
    except timeout.TimedOutExc:
        print "(Caught TimedOutExc, so cleaning up) - ",
        os.system('killall num2sat')
        os.system('killall minisat')
        os.system('killall release-search')
        os.system('killall num2sat')
        os.system('killall minisat')
        os.system('killall release-search')

if use_lama:
    try:
        run_timed(run_lama, Loc)
    except:
        run_timed(run_lama, os.getcwd())
else:
    try:
        run_timed(run_num2sat, Loc)
    except:
        run_timed(run_num2sat, os.getcwd())

print 'use_lama',  use_lama
