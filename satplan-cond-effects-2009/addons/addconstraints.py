import sys
import os

CNF_nf=sys.argv[1]
action_table_nf=sys.argv[2]
CNF_new_nf=CNF_nf+'.new'

first_line = ""

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
    if header_cnf[0] == 'c':
	first_line = header_cnf


########################################
# Se obtienen nuevas clausulas
########################################

new_clauses =[]
at=open(action_table_nf,'r')
temp = []
for l in at:
	s = l.split()
	if (s[-1]=="B)"):
		if (s[-2]=="(ONTABLE"):
			print s
			temp.append(s[2])
print temp
at.close()

########################################
# Saving new CNF
########################################

cnf_new_f=open(CNF_new_nf,'w')
cnf_new_f.write(first_line)
cnf_new_f.write("p cnf %d %d\n" % (orig_vars, orig_clauses+len(new_clauses)) )
#old clauses
for l in CNF:
    cnf_new_f.write(l)
#new clauses
for cls in new_clauses:
    for lit in cls:
        cnf_new_f.write(str(lit)+' ')
    cnf_new_f.write('\n')

constraints=open('constraints.txt','r')
for i in constraints:
	print i

for i in temp:
	print i
	cnf_new_f.write(str(i)+' ')
cnf_new_f.write('0\n')

cnf_new_f.close()
os.system("mv CNF.new CNF")
