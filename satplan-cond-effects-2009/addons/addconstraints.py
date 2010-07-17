import sys
import os
import re
import itertools
import math

def is_cons(a):
    cons = ["always","sometimes","at end","at-most-once","sometimes-after","sometimes-before"]
    for i in range(0,len(cons)):
        if a==cons[i]:
            return i
    return -1

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

########################################
# Se guarda el nuevo CNF
########################################

cnf_new_f=open(CNF_new_nf,'w+')
cnf_new_f.write(first_line)
cnf_new_f.write("p cnf %d %d\n" % (orig_vars, orig_clauses*orig_clauses) )

# Aqui deberia ir la llamada a la funcion o algo a la parte de marion

result = ["sometimes-before","ON C D","CLEAR A"]

########################################
# Se obtienen nuevas clausulas
########################################

for cont in range(0,len(result)):
    codcons = is_cons(result[cont])
    if codcons != -1:
        # 0 always
        # 1 sometimes
        # 2 at end
        # 3 at-most-once
        # 4 sometimes-after
        # 5 sometimes-before
        
        varcons = result[cont]

        temp = []
        temp1 = []
        temp2 = []

        at=open(action_table_nf,'r')
        # El caso que sea sometimes-after
        # o sometimes-before
        if ( (is_cons(varcons)==4) | (is_cons(varcons)==5)):
            varcons1 = result[cont+1]
            varcons2 = result[cont+2]
            for l in at:
                s = l.split()
                if (s[0]=="fluent"):
                    if (re.search(varcons1,l)):
                        print l
                        ls1 = l.split(":")
                        lstime = ls1[0].split(" ")
                        itime = int(lstime[1])
                        ls2 = ls1[1].split("(")
                        numvar = ls2[0]
                        numvar = numvar.lstrip()
                        numvar = numvar.rstrip()
                        temp1.append([numvar,itime])
                    if (re.search(varcons2,l)):
                        print l
                        ls1 = l.split(":")
                        lstime = ls1[0].split(" ")
                        itime = int(lstime[1])
                        ls2 = ls1[1].split("(")
                        numvar = ls2[0]
                        numvar = numvar.lstrip()
                        numvar = numvar.rstrip()
                        temp2.append([numvar,itime])
            cont = cont + 3
        # El caso que sea always, sometimes,
        # at-end o at-most-once
        else:
            varcons1 = result[cont+1]
            for l in at:
                s = l.split()
                if (s[0]=="fluent"):
                    if (re.search(varcons1,l)):
                        ls1 = l.split(":")
                        ls2 = ls1[1].split("(")
                        numvar = ls2[0]
                        numvar = numvar.lstrip()
                        numvar = numvar.rstrip()
                        temp.append(numvar)
            cont=cont+2
        at.close()

        # Se imprimen las clausulas viejas
        # y las nuevas se imprimen en otro 
        # archivo para mantenerlas
        for l in CNF:
            cnf_new_f.write(l)

########################################
# Constraint segun el caso
########################################

        # Caso always
        if (codcons == 0):
            for lit in temp:
                faux.write(str(lit)+' 0\n')

        # Caso sometimes
        elif (codcons == 1):
            for lit in temp:
                faux.write(str(lit)+' ')
            faux.write('0\n')

        # Caso at end
        elif (codcons == 2):
            cnf_new_f.write(temp[-1]+' 0\n')

        # Caso at-most-once
        elif (codcons == 3):
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

            lo = c
            lt = c

            for i in range(0,len(temp)):
                lt = itertools.product(lo,lt)
                lt.replace("(","")
                lt.replace(")","")

            for p in lt:                
                print p

            print '\n\n**********\n\n'

        # Caso sometimes-after
        elif (codcons == 4):
            print '\n\n**********\n\n'

            faux.write('-'+str(temp1[-1][0])+' ')
            print '-',temp1[-1][0],
            limit = temp1[-1][1]
            maxvar = min(limit,len(temp2))
            for it1 in range(0,maxvar):
                if (temp1[it1][1]<temp1[-1][1]):
                    faux.write(str(temp2[it1][0])+' ')
                    print temp2[it1][0],
            print
            faux.write('0\n')
                            
            print temp1
            print temp2
            print '\n\n**********\n\n'

        # Caso sometimes-before
        elif (codcons == 5):
            print '\n\n**********\n\n'

            faux.write('-'+str(temp2[-1][0])+' ')
            print '-',temp2[-1][0],
            limit = temp2[-1][1]
            maxvar = min(limit,len(temp1))
            for it1 in range(0,maxvar):
                if (temp1[it1][1]<temp2[-1][1]):
                    faux.write(str(temp1[it1][0])+' ')
                    print temp1[it1][0],
            print
            faux.write('0\n')
                            
            print temp1
            print temp2
            print '\n\n**********\n\n'

# Imprimo las clausulas acumuladas en el archivo auxiliar
# en el nuevo CNF

faux.close()
faux = open("auxiliar.txt","r")

for i in faux:
    cnf_new_f.write(i)

faux.close()
cnf_new_f.close()
os.system("mv CNF.new CNF")
