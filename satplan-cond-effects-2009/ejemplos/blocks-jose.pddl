(define (problem BLOCKS-4-0)

(:domain BLOCKS)

(:objects D B A C - block)

(:INIT 	(ON B A)
	(CLEAR D)
	(CLEAR C)    
	(CLEAR B)  
	(ONTABLE A)
	(ONTABLE C) 
	(ONTABLE D)  
	(HANDEMPTY))

(:goal (ON A B) )

;(:constraints (always CLEAR D)
;
;)
;
;
;)

)