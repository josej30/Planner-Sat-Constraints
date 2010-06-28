import sys
import re
import os

f = open(sys.argv[1], 'rw')
f2 = open("constraints.txt", 'w')
f3 = open("temp.txt", 'w')

found = "false"

os.system("cp "+sys.argv[1]+" problem-original.pddl")

for line in f:
	temp = line.split(':')
	for i in temp:
		temp2 =	i.split(' ')
		for j in temp2:
			if (j == "constraints"):
				if (line[0]!=";"):
					found = "true"
	if (found=="true"):
		f2.write(line)
		f3.write(";%s" % (line))
	else:
		f3.write(line)
if (found=="true"):
	f3.write("\n)")

f.close
f2.close
f3.close

os.system("mv temp.txt "+sys.argv[1])
