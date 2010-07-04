(define (domain Depot-object-fluents)
(:requirements :typing :equality :fluents)
(:types place locatable - object
	depot distributor - place
        truck hoist surface - locatable
        pallet crate - surface)

(:predicates (lifting ?x - hoist ?y - crate)
             (available ?x - hoist)
             (clear ?x - surface)
)

(:functions 
	(load_limit ?t - truck) 
	(current_load ?t - truck) 
	(weight ?c - crate)
	(fuel-cost) - number
	(position-of ?x - locatable) - place
	(on-top-of ?x - crate) - (either surface truck hoist)
)

	
(:action Drive
:parameters (?x - truck ?z - place) 
:effect (and (assign (position-of ?x) ?z)
		(increase (fuel-cost) 10)))


(:action Lift
:parameters (?x - hoist ?y - crate)
:precondition (and (= (position-of ?x) (position-of ?y)) (available ?x) (clear ?y))
:effect (and (lifting ?x ?y) (not (available ?x)) 
             (clear ?z) (assign (on-top-of ?y) ?x) (assign (position-of ?y) undefined) (increase (fuel-cost) 1)))

(:action Drop 
:parameters (?x - hoist ?y - crate ?z - surface)
:precondition (and (= (position-of ?x) (position-of ?z)) (clear ?z) (lifting ?x ?y))
:effect (and (available ?x) (not (lifting ?x ?y)) (assign (position-of ?y) (position-of ?z)) (not (clear ?z))
		(assign (on-top-of ?y) ?z)))

(:action Load
:parameters (?x - hoist ?y - crate ?z - truck)
:precondition (and (= (position-of ?x) (position-of ?z)) (lifting ?x ?y)
		(<= (+ (current_load ?z) (weight ?y)) (load_limit ?z)))
:effect (and (not (lifting ?x ?y)) (assign (on-top-of ?y) ?z) (available ?x)
		(increase (current_load ?z) (weight ?y))))

(:action Unload 
:parameters (?x - hoist ?y - crate ?z - truck)
:precondition (and (= (position-of ?x) (position-of ?z)) (available ?x) (= (on-top-of ?y) ?z))
:effect (and (assign (on-top-of ?y) ?x) (not (available ?x)) (lifting ?x ?y)
		(decrease (current_load ?z) (weight ?y))))

)
