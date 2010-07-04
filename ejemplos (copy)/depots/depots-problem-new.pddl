(define (problem depotprob1818) (:domain Depot)
(:objects
	depot0 - Depot
	distributor0 distributor1 - Distributor
	truck0 truck1 - Truck
	pallet0 pallet1 pallet2 - Pallet
	crate0 crate1 - Crate
	hoist0 hoist1 hoist2 - Hoist)
(:init
	(= (position-of pallet0) depot0)
	(clear crate1)
	(= (position-of pallet1) distributor0)
	(clear crate0)
	(= (position-of pallet2) distributor1)
	(clear pallet2)
	(= (position-of truck0) distributor1)
	(= (current_load truck0) 0)
	(= (load_limit truck0) 323)
	(= (position-of truck1) depot0)
	(= (current_load truck1) 0)
	(= (load_limit truck1) 220)
	(= (position-of hoist0) depot0)
	(available hoist0)
	(= (position-of hoist1) distributor0)
	(available hoist1)
	(= (position-of hoist2) distributor1)
	(available hoist2)
	(= (position-of crate0) distributor0)
	(= (on-top-of crate0) pallet1)
	(= (weight crate0) 11)
	(= (position-of crate1) depot0)
	(= (on-top-of crate1) pallet0)
	(= (weight crate1) 86)
	(= (fuel-cost) 0)
)

(:goal (and
		(= (on-top-of crate0) pallet2)
		(= (on-top-of crate1) pallet1)
	)
)

(:metric minimize (fuel-cost)))
