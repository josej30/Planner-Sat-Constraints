#! /usr/bin/env python2.5
# -*- coding: latin-1 -*-

import sys
import os
import subprocess
import marshal

CNF_nf=sys.argv[1]
action_table_nf=sys.argv[2]
observations_nf=sys.argv[3]
CNF_new_nf=CNF_nf+'.new'

if len(sys.argv) > 4 and sys.argv[4] == 'z':
    solver='z'
elif len(sys.argv) > 4 and sys.argv[4] == 'm':
    solver='m'
else:
    print "argument number 4 can be 'm' for minisat 'z' for zchaff: ", sys.argv[4]
    sys.exit(0)

if len(sys.argv) > 5 and sys.argv[5] == 'd':
    debug=True
else:
    debug=False

debug2=debug
if debug:
    print sys.argv

# Loading old CNF
CNF=file(CNF_nf)
line_ok = False
while not line_ok:
    header_cnf=CNF.readline()
    if header_cnf[0] == 'p':
        line_ok = True
        header_cnf = header_cnf.split()
        orig_vars = int(header_cnf[2])
        orig_clauses = int(header_cnf[3])

def has_obs(s):
    return False

########################################
# Stationarity
########################################

var2txt={}
action2id={}
fluent_horiz2id={}
action2var={}
obs2action={}
max_horiz = -1
current_var = orig_vars
for l in file(action_table_nf):
    l = l.split()

    name = l[3]#[1:-1] #ojo: quitar el [1:-1], deberia funcionar

    horiz=l[1]
    var2txt[id] = horiz+name
    horiz=int(horiz[:-1])
    max_horiz = max(max_horiz,horiz)

    id=int(l[2])

    if l[0].startswith('act'):
        result = has_obs(name)
        if result is not False:
            obs2action[obs].add(name)
            if name not in action2id:
                action2id[name] = []
            action2id[name].append(id)
            if name not in action2var:
                current_var += 1
                action2var[name] = int(current_var)
                var2txt[int(current_var)] = name
    elif l[0].startswith('fluent'):
        fluent_horiz2id[(name,horiz)] = id


new_clauses =[]
# every cnf-var-action enforces the stationary policy var
for act in action2id:
    for id in action2id[act]:
        cls = [-id,action2var[act],0]
        new_clauses.append(cls)

if debug:
    print orig_vars, orig_clauses
    print
    print 'action2id'
    for a in action2id:
        print a, ":", action2id[a]
    print
    print 'action2var'
    for a in action2var:
        print a, ":", action2var[a]
    print
    print observations
#     print
#     print 'var2txt'
#     for v in var2txt:
#         print v, ":", var2txt[v]

 
if debug2:
    print
    print '----------------------------------------'
    print 'NEW CLAUSES!'
    print
    for cls in new_clauses:
        for lit in cls:
            if lit > 0:
                print str(var2txt[lit])+'   ',
            elif lit <> 0:
                print "-"+str(var2txt[-lit])+'   ',
        print
    sys.exit(0)

########################################
# New mutex between 
#     Ko/s0 and Ko'/s0
#     Kq/s0 and Kq'/s0
########################################

#print fluent_horiz2id
debug_mutex_fluent = False
def gen_mutex(klt1, klt2):
    #print 'Generando mutex',klt1, klt2
    s_klt1 = long2short[klt1]
    s_klt2 = long2short[klt2]
    if debug_mutex_fluent:
        print 'Generando mutex',s_klt1, s_klt2
    for i in range(0,max_horiz+1):
        if (s_klt1,i) in fluent_horiz2id and (s_klt2,i) in fluent_horiz2id:
            cls = [-fluent_horiz2id[(s_klt1,i)], -fluent_horiz2id[(s_klt2,i)], 0]
            if debug_mutex_fluent:
                print 'Es decir',cls
            new_clauses.append(cls)



# sys.exit(0)

########################################
# Saving new CNF
########################################

cnf_new_f=open(CNF_new_nf,'w')
cnf_new_f.write("p cnf %d %d\n" % (current_var, orig_clauses+len(new_clauses)) )
#old clauses
for l in CNF:
    cnf_new_f.write(l)
#new clauses
for cls in new_clauses:
    for lit in cls:
        cnf_new_f.write(str(lit)+' ')
    cnf_new_f.write('\n')
cnf_new_f.close()

########################################
# Finally, calling SAT solver
########################################

num2satpath = '/home/hlp/num2sat'
try:
    os.remove('SATRES')
except:
    pass
if solver=='z':
    cmd = '%s/solvers/zchaff/zchaff'
elif solver=='m':
    cmd = '%s/solvers/minisat/MiniSat_v1.14/minisat'
try:
    print cmd % num2satpath
    p = subprocess.Popen([cmd % num2satpath, CNF_new_nf])
    res = p.wait()
except:
    p = subprocess.Popen([cmd % os.getcwd(),CNF_new_nf])
    res = p.wait()

