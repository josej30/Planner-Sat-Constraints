f = open("constraints.txt", 'r')

constraint = ""

# Se mete todo el constraint dentro de un string para parsearlo mas facilmente
for line in f:
	line = line.lstrip() # se le quita la identacion
	line = line.rstrip() # se le quita cualquier espacio y salto de linea al final
	constraint = constraint + line # se va acumulando el constraint

# Se limpian las cosas que no queremos = "(:constraints" ")"
ind = constraint.index(' ')
constraint = constraint[ind:]
constraint = constraint.lstrip()
constraint = constraint[0:-1]
print constraint
