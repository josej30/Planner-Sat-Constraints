(define (problem BLOCKS-4-0)

(:domain BLOCKS)

(:objects D B A C - block)

(:INIT 	(ON D C) 
	(ON C B) 
	(ON B A)
	(CLEAR D)  
	(ONTABLE A) 
	(HANDEMPTY))

(:goal (AND (ON D B) (ON C A) (ON B C)))

(:constraints (always CLEAR D)

)

)
