import sys
import os
import re
import itertools

CNF_nf=sys.argv[1]
action_table_nf=sys.argv[2]
CNF_new_nf=CNF_nf+'.new'
faux = open('auxiliar.txt','a')

first_line = ""

# Loading old CNF
CNF=open(CNF_nf,'r')
line_ok = False
while not line_ok:
    header_cnf=CNF.readline()
    if header_cnf[0] == 'p':
        line_ok = True
        header_cnf = header_cnf.split()
        orig_vars = int(header_cnf[2])
        orig_clauses = int(header_cnf[3])
    if header_cnf[0] == 'c':
	first_line = header_cnf

#########################################
# Se obtienen los constraints del archivo
#########################################

# Aqui deberia ir la llamada a la funcion o algo a la parte de marion

# 0 always
# 1 sometimes
# 2 at end
# 3 at-most-once
# 4 sometimes-after
# 5 sometimes-before
codcons = 2

varcons = "ON D A"

########################################
# Se obtienen nuevas clausulas
########################################

at=open(action_table_nf,'r')
temp = []
for l in at:
    s = l.split()
    if (s[0]=="fluent"):
        if (re.search(varcons,l)):
            ls1 = l.split(":")
            ls2 = ls1[1].split("(")
            numvar = ls2[0]
            numvar = numvar.lstrip()
            numvar = numvar.rstrip()
            temp.append(numvar)
at.close()

########################################
# Se guarda el nuevo CNF
########################################

cnf_new_f=open(CNF_new_nf,'w+')
cnf_new_f.write(first_line)

if (codcons==3):
    orig_clauses = orig_clauses+(len(temp))

cnf_new_f.write("p cnf %d %d\n" % (orig_vars, orig_clauses) )

# Se imprimen las clausulas viejas
for l in CNF:
    cnf_new_f.write(l)

# Las nuevas se imprimen en otro archivo para mantenerlas

# Caso sometimes
if (codcons == 1):
    for lit in temp:
        faux.write(str(lit)+' ')
    faux.write('0\n')

# Caso always
if (codcons == 0):
    for lit in temp:
        faux.write(str(lit)+' 0\n')

# Caso at end
if (codcons == 2):
    print '\n\n**********\n\n'
    cnf_new_f.write(temp[-1]+' 0\n')
    print '\n\n**********\n\n'

# Caso at-most-once
if (codcons == 3):
    print '\n\n**********\n\n'

    c = []
    for i in range(0,len(temp)):
        t = []
        for j in range(0,len(temp)):
            if i==j:
                t.append(str(temp[j]))
            else:
                t.append('-'+str(temp[j]))
        c.append(t)
#    print c

    l = []
    for i in range(0,len(temp)):
        l.append(i)
    a = list(itertools.product(l,repeat=len(temp)))
    for i in a:
        for j in range(0,len(temp)):
#            print c[j][i[j]],
            faux.write(c[j][i[j]]+' ')
        faux.write(' 0\n')
#        print
                        
    print '\n\n**********\n\n'

# Imprimo las clausulas acumuladas en el archivo auxiliar
# en el nuevo CNF

faux.close()
faux = open("auxiliar.txt","r")

for i in faux:
    print i
    cnf_new_f.write(i)

faux.close()
cnf_new_f.close()
os.system("mv CNF.new CNF")
