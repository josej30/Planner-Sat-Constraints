import os

f = open("constraints.txt", 'r')
f2 = open("constraintemp.txt","w")

constraint = ""

existe = 0

# Se mete todo el constraint dentro de un string para parsearlo mas facilmente
for line in f:
	existe = 1
	line = line.lstrip() # se le quita la identacion
	line = line.rstrip() # se le quita cualquier espacio y salto de linea al final
	constraint = constraint + line # se va acumulando el constraint

if (existe == 1):
# Se limpian las cosas que no queremos = "(:constraints" ")"
	ind = constraint.index(' ')
	constraint = constraint[ind:]
	constraint = constraint.lstrip()
	constraint = constraint[0:-2]

f2.write(constraint)

f.close()
f2.close()

os.system("mv constraintemp.txt constraints.txt")
