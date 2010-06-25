

/*
 * THIS SOURCE CODE IS SUPPLIED  ``AS IS'' WITHOUT WARRANTY OF ANY KIND, 
 * AND ITS AUTHOR AND THE JOURNAL OF ARTIFICIAL INTELLIGENCE RESEARCH 
 * (JAIR) AND JAIR'S PUBLISHERS AND DISTRIBUTORS, DISCLAIM ANY AND ALL 
 * WARRANTIES, INCLUDING BUT NOT LIMITED TO ANY IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, AND
 * ANY WARRANTIES OR NON INFRINGEMENT.  THE USER ASSUMES ALL LIABILITY AND
 * RESPONSIBILITY FOR USE OF THIS SOURCE CODE, AND NEITHER THE AUTHOR NOR
 * JAIR, NOR JAIR'S PUBLISHERS AND DISTRIBUTORS, WILL BE LIABLE FOR 
 * DAMAGES OF ANY KIND RESULTING FROM ITS USE.  Without limiting the 
 * generality of the foregoing, neither the author, nor JAIR, nor JAIR's
 * publishers and distributors, warrant that the Source Code will be 
 * error-free, will operate without interruption, or will meet the needs 
 * of the user.
 */









/*********************************************************************
 * File: CNF.c
 * Description: functions for transforming fully-fledged RPG
 *              into a propositional CNF.
 *
 * Author: Joerg Hoffmann 2006
 *
 *********************************************************************/ 









#include "num2sat.h"

#include "output.h"
#include "memory.h"

#include "inst_pre.h"

#include "RPG.h"
#include "RPGvaluetuples.h"

#include "CNF.h"















/* Turns the fully-fledged numeric RPG into a CNF formula, as follows:
 *
 *
 * There are time steps t, of which the last, goalt, contains only facts p and
 * fluents x, not actions/effects. The numeric part of any prec/con is
 * a conjunction of constraints (exp com exp'). There are decision variables for facts at t, 
 * fluent (numeric var) values at t, actions at t,
 * effects at t (1 iff this effect will happen at t), 
 * constraints at t, and constraint value tuples at t (one var for each value tuple satisfying each constraint
 * at each time step).
 *
 *
 * Alternative: talk about "psis" which are the conjunctions of constraints as appear 
 * in the preconditions/eff conditions/goals. turned off be default since it is quite stupid
 * when the conjunctions are large and their constraints don't share many variables
 * (you'll enumerate all value triples for a psi like (x>0 && y>0 && z>0)
 *
 *
 *
 * clauses:
 *
 *
 * init: for p in I: (p_0); for all x: ( (x=I(x))_0 )
 *
 * 
 * constr 1 at t iff one of its value tuples is 1 at t
 * constr: for all t, constr: (-constr_t or OR{constrvt_t | constrvt in tuples(constr)_t})
 *                            for all constrvt in tuples(constr)_t: (-constrvt_t or constr_t)
 *
 * constr value tuple 1 at t iff the tuple holds at t
 * constrvt: for all t, constr, constrvt in tuples(constr)_t:  
 *                      ({-(x=c)_t | (x=c) in constrvt} or constrvt_t)
 *                      for all (x=c) in constrvt: (-constrvt_t or (x=c)_t)
 *
 *
 * action implies precondition
 * pre: for all t\goalt, a in A_t, z in pre(a): (-a_t or z_t) [z == fact or z == constr]
 * effect implies effect condition
 * con: for all t\goalt, e in E_t, z in con(e): (-e_t or z_t) [z == fact or z == constr]
 *
 *
 * effect e implies its action a(e)
 * ea: for all t\goalt, e in E_t: (-e_t or a(e)_t)
 * action implies its effects unless one of their conditions is false
 * ae: for all t\goalt, a in A_t, e in E(a) \cap E_t: (-a_t or OR{-z_t | z in con(e)} or e_t) [z == fact or z == constr]
 *
 *
 * effect implies its effects on the world state
 * eff: for all t\goalt, e in E_t: f.a. p in add(e): (-e_t or p_t+1)
 *                                 f.a. p in del(e): (-e_t or -p_t+1)
 *
 *      this here says that, for e with x := y + 2, e.g. (either not e_t or not (y=1)_t or (x=3)_t+1)
 *      for all t\goalt, e in E_t, (x := exp(barx)) in e, 
 *                     f.a. barc in barx tuples at t that comply with at least one 
 *                          tuple satisfying pre(a(e)) \wedge con(e) at t:
 *                          (-e_t or OR{-(xi=ci) | (xi=ci) in barc} or (x=exp(barc))_t+1)
 *
 *
 *        facts keep their values unless affected in the opposite way 
 * frame: for all t\goalt, p in P_t: (-p_t or OR{e_t | p in del(e)} or p_t+1)
 *                                   (p_t or OR{e_t | p in add(e)} or -p_t+1)
 *        for all t\goalt, p not in P_t, p in P_t+1:  (OR{e_t | p in add(e)} or -p_t+1)
 *
 *        similar for fluents
 *        for all t\goalt, x, c in V(x)_t: (-(x=c)_t or OR{e_t | e affects x} or (x=c)_t+1)
 *                                         ((x=c)_t or OR{e_t | e affects x} or -(x=c)_t+1)
 *        for all t\goalt, x, c not in V(x)_t, c in V(x)_t+1: (OR{e_t | e affects x} or -(x=c)_t+1)
 *
 *
 * goal: for all z in G: (z_goalt)
 *
 * aemutex: for all t\goalt, a in A_t, e in E_t\E(a), a\not|e: (-a_t, -e_t)
 * eemutex: for all t\goalt, e1, e2 in E_t, e1\not|e2: (-e1_t, -e2_t)
 *
 * vmutex: for all t\goalt, x, c1, c2 in V(x)_t, c1 \neq c2: (-(x=c1)_t, -(x=c2)_t)
 *
 * a\not|e :iff pre(a) \cap del(e) not empty, or pre(a) mentions x affected by e
 *
 * e1\not|e2 :iff 1. (con(e1) cup add(e1)) cap del(e2) not empty, or vice versa, or
 *                2. a(e1) \neq a(e2), and (con(e1) cup effect rhs exps e1) mention x affected by e2, or vv, or                
 *                3. an x is affected by both e1 and e2, where not both are := effects.
 *
 * 
 * NOTE that we disallow parallel application of actions/effects affecting the same var x,
 * unless they are of the form (x := exp1) and (x := exp2), in which case the parallel application
 * will be interpreted as saying x_t+1 = exp1_t if exp1_t = exp2_t, and contradiction otherwise. 
 *
 * This is restrictive in that commutative effects could actually be executed in parallel.
 * PDDL2.1 allows for a restrictive form of this, namely if both effects on x are either
 * += or -= (while still postulating cond 2., ensuring that the effect rhs are independent).
 * Here modeling the right mutex clauses is easy but modelling eff becomes hard when
 * alowing such parallelity: the value of x at t+1 will depend on what *subset* of actions
 * affecting it is applied. skip that for now. NOTE also that, should one ever decide to put that in,
 * the RPG building itself would have to be adapted accordingly. 
 *
 *
 * NOTE also that we have several unit clauses in this encoding, which is obviously
 * unnecessary: initial and goal clauses. made so just to make the code look nicer
 * and let the sat solver do the special cases by one step of UP.
 *
 * 
 * NOTE finally, **more importantly than above**: there is often a lot of stuff
 * that isn't actually relevant for the goal, in the sense that it cannot be reached by
 * a full breadth bwd chaining from there. this stuff is (I think right now) NOT easily
 * present in this CNF (in other encodings, the pure literal rule can cope with this, but not
 * here) and **should be removed prior to building the CNF**. method would be to simple use 
 * a marker at every entity, saying whether or not it is actually relevant. markers to be
 * set after RPG is built. postpone to future work...
 *
 */




















/* -------------------------------------------------------------------------------
 * main overlooking functions.
 */



















/* this creates the initial, psi and psivt clauses as specified
 * in the RPGlayer, appends them to the CNF end,
 * and sets the CNF end to the new end. updates nrs.
 */
void CNF_initialize(RPGlayer *t, 
		    CNF **cnfend,
		    int *numvars,
		    int *numclauses)

{

  CNF *clause;
  
  RPGfact *p;

  /* the start CNFid: 1 larger than the nr of vars (initially: 0/1)
   */
  int CNFid = (*numvars) + 1;

  int i;



  /* first, set the new CNFids that we are gonna need.
   */

  /* all present facts.
   */
  for ( p = t->P->next; p; p = p->next ) {
    if ( p->CNFid != -1 ) {
      printf("\ndouble setting CNFid fact?");
      exit( 1 );
    }
    p->CNFid = CNFid++;
  }
  /* all present var values.
   */
  for ( i = 0; i < gnum_relevant_fluents; i++ ) {
    if ( !t->V[i]->next ) {
      /* happens for initially undefined fluents.
       */
      continue;
    }
    /* at most one value in ini state!
     */
    if ( t->V[i]->next->CNFid != -1 ) {
      printf("\ndouble setting CNFid var value?");
      exit( 1 );
    }
    t->V[i]->next->CNFid = CNFid++;
    if ( t->V[i]->next->next ) {
      printf("\nvar > 1 ini value?\n\n");
      exit( 1 );
    }
  }



  if ( gcmd_line.CNFencoding == 0 ) {
    /* all constraints that have a satisfying tuple in here.
     * 
     * have to make space first and initialize (redundant but nicer)
     */
    t->constraint_CNFid = ( int * ) calloc(gnum_relevant_constraints, sizeof( int ) );
    for ( i = 0; i < gnum_relevant_constraints; i++ ) {
      t->constraint_CNFid[i] = -1;
    }
    for ( i = 0; i < gnum_relevant_constraints; i++ ) {
      if ( !t->constraint_VT[i]->next ) {
	continue;
      }
      if ( t->constraint_CNFid[i] != -1 ) {
	printf("\ndouble setting CNFid constraint?");
	exit( 1 );
      }
      t->constraint_CNFid[i] = CNFid++;
      if ( t->constraint_VT[i]->next->CNFid != -1 ) {
	printf("\ndouble setting CNFid valuetuple?");
	exit( 1 );
      }
      t->constraint_VT[i]->next->CNFid = CNFid++;
      /* at most one tuple in ini state!
       */
      if ( t->constraint_VT[i]->next->next ) {
	printf("\nconstraint > 1 ini value tuple?\n\n");
	exit( 1 );
      }
    }
  }
  if ( gcmd_line.CNFencoding == 1 ) {
    /* all psis that have a satisfying tuple in here.
     * 
     * have to make space first and initialize (redundant but nicer)
     */
    t->psi_CNFid = ( int * ) calloc(gnum_relevant_psis, sizeof( int ) );
    for ( i = 0; i < gnum_relevant_psis; i++ ) {
      t->psi_CNFid[i] = -1;
    }
    for ( i = 0; i < gnum_relevant_psis; i++ ) {
      if ( !t->psi_VT[i]->next ) {
	continue;
      }
      if ( t->psi_CNFid[i] != -1 ) {
	printf("\ndouble setting CNFid psi?");
	exit( 1 );
      }
      t->psi_CNFid[i] = CNFid++;
      if ( t->psi_VT[i]->next->CNFid != -1 ) {
	printf("\ndouble setting CNFid valuetuple?");
	exit( 1 );
      }
      t->psi_VT[i]->next->CNFid = CNFid++;
      /* at most one tuple in ini state!
       */
      if ( t->psi_VT[i]->next->next ) {
	printf("\npsi > 1 ini value tuple?\n\n");
	exit( 1 );
      }
    }
  }
  *numvars = CNFid-1;



  /* get the initial-fact clauses.
   */
  for ( p = t->P->next; p; p = p->next ) {
    clause = new_CNF();
    clause->CNFid = ( int * ) calloc(1, sizeof( int ) );
    clause->sign = ( Bool * ) calloc(1, sizeof( Bool ) );
    clause->num = 1;
    clause->CNFid[0] = p->CNFid;
    clause->sign[0] = TRUE;
    clause->prev = *cnfend;
    (*cnfend)->next = clause;
    *cnfend = clause;
    (*numclauses)++;
  }

  /* get the initial-value clauses.
   */
  for ( i = 0; i < gnum_relevant_fluents; i++ ) {
    if ( !t->V[i]->next ) {
      continue;
    }
    clause = new_CNF();
    clause->CNFid = ( int * ) calloc(1, sizeof( int ) );
    clause->sign = ( Bool * ) calloc(1, sizeof( Bool ) );
    clause->num = 1;
    clause->CNFid[0] = t->V[i]->next->CNFid;
    clause->sign[0] = TRUE;
    clause->prev = *cnfend;
    (*cnfend)->next = clause;
    *cnfend = clause;
    (*numclauses)++;
  }

  if ( gcmd_line.CNFencoding == 0 ) {
    /* get the constraint and constraintvt clauses. just take the general 
     * fn call.
     */
    CNF_get_constraint_constraintvt(t, cnfend, numclauses);
  }

  if ( gcmd_line.CNFencoding == 1 ) {
    /* get the psi and psivt clauses. just take the general 
     * fn call.
     */
    CNF_get_psi_psivt(t, cnfend, numclauses);
  }

}



/* this creates the:
 *    pre, con clauses at t,
 *    ea, ae clauses at t,
 *    eff and frame clauses at t->t+1,
 *    action/effect mutex clauses at t.
 *    psi and psivt clauses at t+1,
 *    value mutex clauses at t+1,
 * appends to cnf end, updates cnf end. updates nrs.
 */
void CNF_extend(RPGlayer *t, 
		CNF **cnfend,
		int *numvars,
		int *numclauses)

{

  RPGaction *a;
  RPGeffect *e;
  RPGfact *p;
  RPGvalue *v;
  RPGvaluetuple *vt;
  RPGlayer *tpp = t->next;

  int CNFid = (*numvars) + 1;

  int i;



  /* first, set the new CNFids that we are gonna need.
   */

  /* actions and effects at t.
   */
  for ( a = t->A->next; a; a = a->next ) {
    if ( a->CNFid != -1 ) {
      printf("\ndouble setting CNFid action?");
      exit( 1 );
    }
    a->CNFid = CNFid++;
    for ( e = a->E->next; e; e = e->next ) {
      if ( e->CNFid != -1 ) {
	printf("\ndouble setting CNFid effect?");
	exit( 1 );
      }
      e->CNFid = CNFid++;
    }
  }

  /* facts and fluents at tpp.
   */
  if ( !tpp ) {
    printf("\nsuccessor layer in CNF extend not there?");
    exit( 1 );
  }
  for ( p = tpp->P->next; p; p = p->next ) {
    if ( p->CNFid != -1 ) {
      printf("\ndouble setting CNFid tpp fact?");
      exit( 1 );
    }
    p->CNFid = CNFid++;
  }
  for ( i = 0; i < gnum_relevant_fluents; i++ ) {
    for ( v = tpp->V[i]->next; v; v = v->next ) {
      if ( v->CNFid != -1 ) {
	printf("\ndouble setting CNFid tpp var value?");
	exit( 1 );
      }
      v->CNFid = CNFid++;
    }
  }
  if ( gcmd_line.CNFencoding == 0 ) {
    tpp->constraint_CNFid = ( int * ) calloc(gnum_relevant_constraints, sizeof( int ) );
    for ( i = 0; i < gnum_relevant_constraints; i++ ) {
      tpp->constraint_CNFid[i] = -1;
    }
    for ( i = 0; i < gnum_relevant_constraints; i++ ) {
      if ( !tpp->constraint_VT[i]->next ) {
	continue;
      }
      if ( tpp->constraint_CNFid[i] != -1 ) {
	printf("\ndouble setting CNFid tpp constraint?");
	exit( 1 );
      }
      tpp->constraint_CNFid[i] = CNFid++;
      for ( vt = tpp->constraint_VT[i]->next; vt; vt = vt->next ) {
	if ( vt->CNFid != -1 ) {
	  printf("\ndouble setting CNFid tpp valuetuple?");
	  exit( 1 );
	}
	vt->CNFid = CNFid++;
      }
    }
  }
  if ( gcmd_line.CNFencoding == 1 ) {
    tpp->psi_CNFid = ( int * ) calloc(gnum_relevant_psis, sizeof( int ) );
    for ( i = 0; i < gnum_relevant_psis; i++ ) {
      tpp->psi_CNFid[i] = -1;
    }
    for ( i = 0; i < gnum_relevant_psis; i++ ) {
      if ( !tpp->psi_VT[i]->next ) {
	continue;
      }
      if ( tpp->psi_CNFid[i] != -1 ) {
	printf("\ndouble setting CNFid tpp psi?");
	exit( 1 );
      }
      tpp->psi_CNFid[i] = CNFid++;
      for ( vt = tpp->psi_VT[i]->next; vt; vt = vt->next ) {
	if ( vt->CNFid != -1 ) {
	  printf("\ndouble setting CNFid tpp valuetuple?");
	  exit( 1 );
	}
	vt->CNFid = CNFid++;
      }
    }
  }
  *numvars = CNFid-1;



  /* now for the clauses!
   *
   * order of these fn calls doesn't matter.
   */

  /* get the pre and con clauses at t.
   */
  CNF_get_pre_con(t, cnfend, numclauses);

  /* get the ea and ae clauses at t.
   */
  CNF_get_ea_ae(t, cnfend, numclauses);

  /* get the eff clauses at t -> tpp.
   */
  CNF_get_eff(t, cnfend, numclauses);

  /* get the frame clauses at t -> tpp.
   */
  CNF_get_frame(t, cnfend, numclauses);

  /* get the a/e mutex clauses at t.
   */
  CNF_get_aemutex(t, cnfend, numclauses);

  /* get the e/e mutex clauses at t.
   */
  CNF_get_eemutex(t, cnfend, numclauses);

  if ( gcmd_line.CNFencoding == 0 ) {
    /* get the constraint and constraintvt clauses at tpp.
     */
    CNF_get_constraint_constraintvt(tpp, cnfend, numclauses);
  }

  if ( gcmd_line.CNFencoding == 1 ) {
    /* get the psi and psivt clauses at tpp.
     */
    CNF_get_psi_psivt(tpp, cnfend, numclauses);
  }

  /* get the v mutex clauses at tpp.
   */
  CNF_get_vmutex(tpp, cnfend, numclauses);

}



/* this creates the goal clauses at t and appends them
 * to the CNF. updates nr of clauses only since no new vars will
 * be added.
 */
void CNF_get_goal(RPGlayer *t, 
		  CNF **cnfend, 
		  int *numclauses)

{

  CNF *clause;

  RPGfact *p;

  int i;

  for ( i = 0; i < gnum_logic_goal; i++ ) {
    /* INEFFICIENT!
     */
    for ( p = t->P->next; p; p = p->next ) {
      if ( p->id == glogic_goal[i] ) {
	break;
      }
    }
    if ( !p ) {
      printf("\ncan't find goal fact in get goal?\n\n");
      exit( 1 );
    }
    clause = new_CNF();
    clause->CNFid = ( int * ) calloc(1, sizeof( int ) );
    clause->sign = ( Bool * ) calloc(1, sizeof( Bool ) );
    clause->num = 1;
    clause->CNFid[0] = p->CNFid;
    clause->sign[0] = TRUE;
    clause->prev = *cnfend;
    (*cnfend)->next = clause;
    *cnfend = clause;
    (*numclauses)++;
  }

  if ( gcmd_line.CNFencoding == 0 ) {
    for ( i = 0; i < gnum_numeric_goal; i++ ) {
      clause = new_CNF();
      clause->CNFid = ( int * ) calloc(1, sizeof( int ) );
      clause->sign = ( Bool * ) calloc(1, sizeof( Bool ) );
      clause->num = 1;
      clause->CNFid[0] = t->constraint_CNFid[ggoal_constraint_id[i]];
      clause->sign[0] = TRUE;      
      clause->prev = *cnfend;
      (*cnfend)->next = clause;
      *cnfend = clause;
      (*numclauses)++;
    }
  }

  if ( gcmd_line.CNFencoding == 1 ) {
    if ( ggoal_psi_id != -1 ) {
      clause = new_CNF();
      clause->CNFid = ( int * ) calloc(1, sizeof( int ) );
      clause->sign = ( Bool * ) calloc(1, sizeof( Bool ) );
      clause->num = 1;
      if ( t->psi_CNFid[ggoal_psi_id] == -1 ) {
	printf("\ngoal psi not CNFid'ed?\n\n");
	exit( 1 );
      }
      clause->CNFid[0] = t->psi_CNFid[ggoal_psi_id];
      clause->sign[0] = TRUE;      
      clause->prev = *cnfend;
      (*cnfend)->next = clause;
      *cnfend = clause;
      (*numclauses)++;
    }
  }

}



/* this removes the goal clauses from the end of the CNF.
 * must be done prior to extending the CNF another step.
 *
 * ATTENTION: this simply removes the right number of clauses
 * from the end of the CNF! use with care!
 *
 * clauses are stored instead of free'ed since free'ing 
 * sometimes behaves strangely and storing these 
 * few clauses doesn't matter at all anyway (avoid memory leaks, though).
 */
void CNF_retract_goal(RPGlayer *t, 
		      CNF **cnfend, 
		      int *numclauses)

{

  static Bool fc = TRUE;

  CNF *clause;

  int i;



  if ( fc ) {
    gCNFtrash = new_CNF();
    gCNFtrashend = gCNFtrash;
    fc = FALSE;
  }



  for ( i = 0; i < gnum_logic_goal; i++ ) {
    clause = *cnfend;
    *cnfend = (*cnfend)->prev;
    (*cnfend)->next = NULL;
    (*numclauses)--;

    gCNFtrashend->next = clause;
    clause->prev = gCNFtrashend;
    gCNFtrashend = clause;
  }

  if ( gcmd_line.CNFencoding == 0 ) {
    for ( i = 0; i < gnum_numeric_goal; i++ ) {
      clause = *cnfend;
      *cnfend = (*cnfend)->prev;
      (*cnfend)->next = NULL;
      (*numclauses)--;
      
      gCNFtrashend->next = clause;
      clause->prev = gCNFtrashend;
      gCNFtrashend = clause;
    }
  }

  if ( gcmd_line.CNFencoding == 1 ) {
    if ( ggoal_psi_id != -1 ) {
      clause = *cnfend;
      *cnfend = (*cnfend)->prev;
      (*cnfend)->next = NULL;
      (*numclauses)--;
      
      gCNFtrashend->next = clause;
      clause->prev = gCNFtrashend;
      gCNFtrashend = clause;
    }
  }

}



/* outputs CNFid table and CNF to stdout.
 * for debugging.
 */
void CNF_print(RPGlayer *rpg,
	       CNF *cnf,
	       int numvars,
	       int numclauses)

{

  CNF *icnf;

  RPGfact *p;
  RPGaction *a;
  RPGeffect *e;
  RPGvalue *v;
  RPGvaluetuple *vt;
  RPGlayer *t;
  
  int i, j;



  /* first print the "code table"
   */
  printf("\n\n-----------------------------RPG CNF codes:");
  for ( t = rpg->next; t; t = t->next ) {
    printf("\nLayer %d:", t->t);

    for ( p = t->P->next; p; p = p->next ) {
      printf("\n%5d: fact ", p->CNFid);
      print_Fact(p->p);
    }

    for ( i = 0; i < gnum_relevant_fluents; i++ ) {
      for ( v = t->V[i]->next; v; v = v->next ) {
	printf("\n%5d: fluentvalue %6.2f = ", v->CNFid, v->v);
	print_Fluent(&(grelevant_fluents[i]));
      }
    }

    if ( gcmd_line.CNFencoding == 0 ) {
      if ( !t->constraint_CNFid ) {
	printf("\nprint request for layer with constraint_CNFid not initialized?\n\n");
	exit( 1 );
      }
      for ( i = 0; i < gnum_relevant_constraints; i++ ) {
	if ( !t->constraint_VT[i]->next ) {
	  continue;
	}
	printf("\n%5d: constraint%d", t->constraint_CNFid[i], i);
	for ( vt = t->constraint_VT[i]->next; vt; vt = vt->next ) {
	  printf("\n%5d: constraintvt", vt->CNFid);
	  for ( j = 0; j < gnum_relevant_fluents; j++ ) {
	    if ( !vt->have[j] ) {
	      continue;
	    }
	    printf(" ");
	    print_Fluent(&(grelevant_fluents[j]));
	    printf(" = %6.2f", vt->vt[j]);
	  }
	} /* vt over satisfying value tuples */
      } /* endfor i over constraints indices */
    }

    if ( gcmd_line.CNFencoding == 1 ) {
      if ( !t->psi_CNFid ) {
	printf("\nprint request for layer with psi_CNFid not initialized?\n\n");
	exit( 1 );
      }
      for ( i = 0; i < gnum_relevant_psis; i++ ) {
	if ( !t->psi_VT[i]->next ) {
	  continue;
	}
	printf("\n%5d: psi%d", t->psi_CNFid[i], i);
	for ( vt = t->psi_VT[i]->next; vt; vt = vt->next ) {
	  printf("\n%5d: psivt", vt->CNFid);
	  for ( j = 0; j < gnum_relevant_fluents; j++ ) {
	    if ( !vt->have[j] ) {
	      continue;
	    }
	    printf(" ");
	    print_Fluent(&(grelevant_fluents[j]));
	    printf(" = %6.2f", vt->vt[j]);
	  }
	} /* vt over satisfying value tuples */
      } /* endfor i over psis indices */
    }

    if ( t->A ) {
      /* not present in last layer!
       */
      for ( a = t->A->next; a; a = a->next ) {
	printf("\n%5d: action ", a->CNFid);
	print_Action_name(a->a);
	for ( e = a->E->next; e; e = e->next ) {
	  printf("\n%5d: effect %d", e->CNFid, e->id);
	}
      }
    }
  } /* endfor t over RPG layers */



  /* now print the CNF.
   */
  printf("\n\n-----------------------------CNF:");
  printf("\nnumvars: %d, numclauses: %d", numvars, numclauses);
  i = 0;
  for ( icnf = cnf->next; icnf; icnf = icnf->next ) {
    printf("\n%5d:", i);
    for ( j = 0; j < icnf->num; j++ ) {
      if ( icnf->sign[j] ) {
	printf(" %d-", icnf->CNFid[j]);
	CNF_print_infostring(rpg, icnf->CNFid[j]);
      } else {
	printf(" NOT%d-", icnf->CNFid[j]);
	CNF_print_infostring(rpg, icnf->CNFid[j]);
      }
    }
    i++;
  }

}



/* help a little in understanding what a code means, *inside*
 * the CNF formula output.
 *
 * awkward, have to walk through entire RPG and look for that CNFid.
 */
void CNF_print_infostring(RPGlayer *rpg, int CNFid)

{

  RPGfact *p;
  RPGaction *a;
  RPGeffect *e;
  RPGvalue *v;
  RPGvaluetuple *vt;
  RPGlayer *t;
  
  int i;



  for ( t = rpg->next; t; t = t->next ) {
    for ( p = t->P->next; p; p = p->next ) {
      if ( p->CNFid == CNFid ) {
	printf("t%d-", t->t); print_Fact(p->p);
	return;
      }
    }
    for ( i = 0; i < gnum_relevant_fluents; i++ ) {
      for ( v = t->V[i]->next; v; v = v->next ) {
	if ( v->CNFid == CNFid ) {
	  printf("t%d-", t->t); printf("%.2f=", v->v);
	  print_Fluent(&(grelevant_fluents[i]));
	  return;
	}
      }
    }
    if ( gcmd_line.CNFencoding == 0 ) {
      if ( !t->constraint_CNFid ) {
	printf("\nprint request for layer with constraint_CNFid not initialized?\n\n");
	exit( 1 );
      }
      for ( i = 0; i < gnum_relevant_constraints; i++ ) {
	if ( !t->constraint_VT[i]->next ) {
	  continue;
	}
	if ( t->constraint_CNFid[i] == CNFid ) {
	  printf("t%d-", t->t); printf("constraint%d", i);
	  return;
	}
	for ( vt = t->constraint_VT[i]->next; vt; vt = vt->next ) {
	  if ( vt->CNFid == CNFid ) {
	    printf("t%d-", t->t); printf("constraint%dvt", i);
	    return;
	  }
	}
      }
    }
    if ( gcmd_line.CNFencoding == 1 ) {
      if ( !t->psi_CNFid ) {
	printf("\nprint request for layer with psi_CNFid not initialized?\n\n");
	exit( 1 );
      }
      for ( i = 0; i < gnum_relevant_psis; i++ ) {
	if ( !t->psi_VT[i]->next ) {
	  continue;
	}
	if ( t->psi_CNFid[i] == CNFid ) {
	  printf("t%d-", t->t); printf("psi%d", i);
	  return;
	}
	for ( vt = t->psi_VT[i]->next; vt; vt = vt->next ) {
	  if ( vt->CNFid == CNFid ) {
	    printf("t%d-", t->t); printf("psi%dvt", i);
	    return;
	  }
	}
      }
    }
    if ( t->A ) {
      for ( a = t->A->next; a; a = a->next ) {
	if ( a->CNFid == CNFid ) {
	  printf("t%d-", t->t); print_Action_name(a->a);	  
	  return;
	}
	i = 0;
	for ( e = a->E->next; e; e = e->next ) {
	  if ( e->CNFid == CNFid ) {
	    printf("t%d-", t->t); printf("eff%d-", i);
	    print_Action_name(a->a);
	    return;
	  }
	  i++;
	}
      }
    } /* endif t->A */
  } /* endfor t over RPG layers */

}



void CNF_statistics(RPGlayer *t, 
		    CNF *cnf,
		    int numvars,
		    int numclauses)

{

  CNF *icnf;
  float sum, meansize;
  int maxsize = 0;

  sum = 0;
  for ( icnf = cnf->next; icnf; icnf = icnf->next ) {
    sum += ((float) icnf->num);
    if ( icnf->num > maxsize ) {
      maxsize = icnf->num;
    }
  }
  meansize = sum / ((float) numclauses);

  printf("\nCNF layer %d: %d vars, %d clauses mean size %.2f max size %d", 
	 t->t, numvars, numclauses, meansize, maxsize);

}



/* outputs file "CNF"
 * in standard format.
 * takes in START of CNF!
 *
 * bound on plan length just for comment printout.
 */
void CNF_output(CNF *cnf,
		int numvars,
		int numclauses,
		int bound)
     
{

  FILE *OUT;

  CNF *icnf;

  int i;



  if ( (OUT = fopen("CNF", "w")) == NULL ) {
    printf("\ncan't open file CNF!\n\n");
    exit( 1 );
  }

  fprintf(OUT, "c CNF from NumPDDL2CNF, bound %d, -p %s -o %s -f %s\n", 
	  bound, gcmd_line.path, gcmd_line.ops_file_name, gcmd_line.fct_file_name);

  fprintf(OUT, "p cnf %d %d\n", numvars, numclauses);

  for ( icnf = cnf->next; icnf; icnf = icnf->next ) {
    for ( i = 0; i < icnf->num; i++ ) {
      if ( icnf->sign[i] ) {
	fprintf(OUT, "%d ", icnf->CNFid[i]);
      } else {
	fprintf(OUT, "-%d ", icnf->CNFid[i]);
      }
    }
    fprintf(OUT, "0\n");
  }

  fclose(OUT);

}



int CNF_output_plan(FILE *SATRES,
		    RPGlayer *rpg,
		    int numvars)

{

  RPGlayer *t;
  RPGaction *a;

  int r, i;
  int nractions = 0;


  printf("\n\nFound plan:");

  for ( i = 1; i <= numvars; i++ ) {
    fscanf(SATRES, "%d\n", &r);

    if ( r == -1 ) {
      printf("\nvar value is -1 in satisfying encoding?\n\n");
      exit( 1 );
    }

    if ( r == 0 ) {
      /* This should mean the var is set to 0
       */
      continue;
    }

    /* see if this is an action in the RPG, and if yes, print it!
     */
    a = NULL;
    for ( t = rpg->next; t->next; t = t->next ) {
      for ( a = t->A->next; a; a = a->next ) {
	if ( a->CNFid == i ) {
	  break;
	}
      }
      if ( a ) {
	break;
      }
    }
    if ( t->next ) {
      if ( !a ) {
	printf("\nfound but not found action?\n\n");
	exit( 1 );
      }
      nractions++;
      printf("\nTime %4d: ", t->t);
      print_Action_name(a->a);
    }
  }

  return nractions;

}

int CNF_print_act_table(RPGlayer *rpg, char* filename)

{
/* aqui */
  RPGlayer *t;
  RPGaction *a = NULL;
  RPGfact *p;
  RPGvalue *v;
  RPGvaluetuple *vt;
  FILE* OUT = NULL;
  
  int nractions = 0, i;

  if ( (OUT = fopen(filename, "w")) == NULL ) {
    printf("\ncan't open file %s!\n\n",filename);
    exit( 1 );
  }

  for ( t = rpg->next; t->next; t = t->next ) {
    for ( p = t->P->next; p; p = p->next ) {
      fprintf(OUT, "fluent %d: ", t->t);
      fprintf(OUT, "%d ", p->CNFid);
      print_Fact_file(OUT, p->p);
      fprintf(OUT, "\n");
    }
    
    for ( a = t->A->next; a; a = a->next ) {
      fprintf(OUT, "act %d: ", t->t);
      fprintf(OUT, "%d ", a->CNFid);
      fprintf(OUT, "(%s)", a->a->name);
      fprintf(OUT, "\n");
    }
  }
  fclose(OUT);
  return nractions;

}

/* 
   returns a string in case the CNFid is an action or an effect
 */
char* get_act_name(RPGlayer *rpg, int CNFid)
{
  RPGaction *a;
  RPGeffect *e;
  RPGlayer *t;
  static Bool fc = TRUE;
  static char **cache = NULL;
  static int last_size;
  int i, new_size;
  const int debug = FALSE;

  if( fc )
    {
      last_size = 1000;
      cache = (char**) calloc( last_size, sizeof(char*));
      fc = FALSE;
    }
  if( CNFid >= last_size - 10 )
    {
      new_size = 1.5 * last_size;
      if( debug )
	printf("Resizing from %d to %d...", last_size, new_size);
      cache = (char**) realloc( cache, new_size * sizeof(char*));
      for( i = last_size; i < new_size; i++ )
	cache[i] = NULL;
      last_size = new_size;
      if( debug )
	printf("done\n");
    }
 
  if(debug)
    {
      printf("Tabla de acts, so far:\n");
      for( i = 0; i < last_size; i++ )
	if( cache[i] != NULL )
	  printf("Act(%d): %s\n", i, cache[i]);
    }
 
  if( cache[CNFid] != NULL )
    return cache[CNFid];
  
  for ( t = rpg; t; t = t->next ) {
    if ( t->A ) {
      for ( a = t->A->next; a; a = a->next ) {
	if ( a->CNFid == CNFid ) {
	  cache[CNFid] = a->a->name;
	  return a->a->name;
	}
	for ( e = a->E->next; e; e = e->next ) {
	  if ( e->CNFid == CNFid ) {
	    cache[CNFid] = a->a->name;
	    return a->a->name;
	  }
	}
      }
    } /* endif t->A */
  } /* endfor t over RPG layers */
  
  return NULL;
}

Bool ignore_this_mutex(RPGlayer *t, int CNFid1, int CNFid2 )
{
  char* name1 = get_act_name(t, CNFid1);
  char* name2 = get_act_name(t, CNFid2);
  if( name1 == NULL || name2 == NULL )
    return FALSE;

  /* char only_keep_mutex_with[]="ZOOM"; */
  if( *only_keep_mutex_with != 0 )
    {
      /* printf("IGNORING %s\n", only_keep_mutex_with); */
      if( strstr(name1,only_keep_mutex_with) || 
	  strstr(name2,only_keep_mutex_with) )
	return FALSE;
      else
	return TRUE;
    }

  Bool debug = FALSE;
  if( debug )
    printf("\nPensando mutex de acciones %s(%d) y %s(%d)\n", name1, CNFid1, name2, CNFid2);
  
  char **mutex;
  for( mutex = mutex2ignore; *mutex; mutex++ )
    if( strstr(name1,*mutex) && strstr(name2,*mutex) )
      {
	if( debug )
	  printf("IGNORANDO\n");
	return TRUE;
      }
  return FALSE;
}






























/* -------------------------------------------------------------------------------
 * getting specific clauses.
 */

























/* the constraint clauses say that any constraint is TRUE iff
 * at least one of its satisfying tuples is TRUE.
 * the constraintvt clauses say that any satisfying tuple is TRUE
 * iff all its x=c constraints are TRUE.
 */
void CNF_get_constraint_constraintvt(RPGlayer *t, 
				     CNF **cnfend, 
				     int *numclauses)

{

  CNF *clause;
  
  RPGvalue *v;
  RPGvaluetuple *vt;

  int i, j, num;



  /* go over all constraints with at least one satisfying tuple.
   */
  for ( i = 0; i < gnum_relevant_constraints; i++ ) {
    if ( !t->constraint_VT[i]->next ) {
      continue;
    }



    /* constraint clauses.
     */

    /* first: (-vt or constraint) for each vt(constraint)
     * count num of tuples as side effect.
     */
    num = 0;
    for ( vt = t->constraint_VT[i]->next; vt; vt = vt->next ) {
      clause = new_CNF();
      clause->CNFid = ( int * ) calloc(2, sizeof( int ) );
      clause->sign = ( Bool * ) calloc(2, sizeof( Bool ) );
      clause->num = 2;
      clause->CNFid[0] = vt->CNFid;
      clause->sign[0] = FALSE;
      clause->CNFid[1] = t->constraint_CNFid[i];
      clause->sign[1] = TRUE;
      clause->prev = *cnfend;
      (*cnfend)->next = clause;
      *cnfend = clause;
      (*numclauses)++;
      num++;
    } /* endfor vt over satisfying value tuples */

    /* now: (-constraint or OR_vt(constraint) vt)
     */
    clause = new_CNF();
    clause->CNFid = ( int * ) calloc(num+1, sizeof( int ) );
    clause->sign = ( Bool * ) calloc(num+1, sizeof( Bool ) );
    clause->num = num+1;
    clause->CNFid[0] = t->constraint_CNFid[i];
    clause->sign[0] = FALSE;
    num = 1;
    for ( vt = t->constraint_VT[i]->next; vt; vt = vt->next ) {
      clause->CNFid[num] = vt->CNFid;
      clause->sign[num] = TRUE;
      num++;
    }
    clause->prev = *cnfend;
    (*cnfend)->next = clause;
    *cnfend = clause;
    (*numclauses)++;



    /* constraintvt clauses.
     */

    for ( vt = t->constraint_VT[i]->next; vt; vt = vt->next ) {
      /* first: (-vt or (x=c)) for each (x=c)(vt)
       *
       * count num of (x=c) as side effect.
       */
      num = 0;
      for ( j = 0; j < gnum_relevant_fluents; j++ ) {
	if ( !vt->have[j] ) {
	  continue;
	}
	clause = new_CNF();
	clause->CNFid = ( int * ) calloc(2, sizeof( int ) );
	clause->sign = ( Bool * ) calloc(2, sizeof( Bool ) );
	clause->num = 2;
	clause->CNFid[0] = vt->CNFid;
	clause->sign[0] = FALSE;
	/* have to find the var value first.
	 */
	for ( v = t->V[j]->next; v; v = v->next ) {
	  if ( v->v == vt->vt[j] ) {
	    break;
	  }
	}
	if ( !v ) {
	  printf("\ndidn't find right v for vt(constraint)?\n\n");
	  exit( 1 );
	}
	clause->CNFid[1] = v->CNFid;
	clause->sign[1] = TRUE;
	clause->prev = *cnfend;
	(*cnfend)->next = clause;
	*cnfend = clause;
	(*numclauses)++;
	num++;
      }
	
      /* now: ((OR_(x=c)(vt) -(x=c)) or vt)
       */
      clause = new_CNF();
      clause->CNFid = ( int * ) calloc(num+1, sizeof( int ) );
      clause->sign = ( Bool * ) calloc(num+1, sizeof( Bool ) );
      clause->num = num+1;
      num = 0;
      for ( j = 0; j < gnum_relevant_fluents; j++ ) {
	if ( !vt->have[j] ) {
	  continue;
	}
	/* INEFFICIENT! could remember this from above. probably benign:
	 * tuples haven't many members.
	 */
	for ( v = t->V[j]->next; v; v = v->next ) {
	  if ( v->v == vt->vt[j] ) {
	    break;
	  }
	}
	if ( !v ) {
	  printf("\ndidn't find right v for vt(constraint)?\n\n");
	  exit( 1 );
	}
	clause->CNFid[num] = v->CNFid;
	clause->sign[num] = FALSE;
	num++;
      }
      clause->CNFid[num] = vt->CNFid;
      clause->sign[num] = TRUE;
      clause->prev = *cnfend;
      (*cnfend)->next = clause;
      *cnfend = clause;
      (*numclauses)++;
    } /* endfor vt over satisfying value tuples */
  } /* endfor i over constraints indices */

}



/* the psi clauses say that any psi is TRUE iff
 * at least one of its satisfying tuples is TRUE.
 * the psivt clauses say that any satisfying tuple is TRUE
 * iff all its x=c constraints are TRUE.
 */
void CNF_get_psi_psivt(RPGlayer *t, 
		       CNF **cnfend, 
		       int *numclauses)

{

  CNF *clause;
  
  RPGvalue *v;
  RPGvaluetuple *vt;

  int i, j, num;



  /* go over all psis with at least one satisfying tuple.
   */
  for ( i = 0; i < gnum_relevant_psis; i++ ) {
    if ( !t->psi_VT[i]->next ) {
      continue;
    }



    /* psi clauses.
     */

    /* first: (-vt or psi) for each vt(psi)
     * count num of tuples as side effect.
     */
    num = 0;
    for ( vt = t->psi_VT[i]->next; vt; vt = vt->next ) {
      clause = new_CNF();
      clause->CNFid = ( int * ) calloc(2, sizeof( int ) );
      clause->sign = ( Bool * ) calloc(2, sizeof( Bool ) );
      clause->num = 2;
      clause->CNFid[0] = vt->CNFid;
      clause->sign[0] = FALSE;
      clause->CNFid[1] = t->psi_CNFid[i];
      clause->sign[1] = TRUE;
      clause->prev = *cnfend;
      (*cnfend)->next = clause;
      *cnfend = clause;
      (*numclauses)++;
      num++;
    } /* endfor vt over satisfying value tuples */

    /* now: (-psi or OR_vt(psi) vt)
     */
    clause = new_CNF();
    clause->CNFid = ( int * ) calloc(num+1, sizeof( int ) );
    clause->sign = ( Bool * ) calloc(num+1, sizeof( Bool ) );
    clause->num = num+1;
    clause->CNFid[0] = t->psi_CNFid[i];
    clause->sign[0] = FALSE;
    num = 1;
    for ( vt = t->psi_VT[i]->next; vt; vt = vt->next ) {
      clause->CNFid[num] = vt->CNFid;
      clause->sign[num] = TRUE;
      num++;
    }
    clause->prev = *cnfend;
    (*cnfend)->next = clause;
    *cnfend = clause;
    (*numclauses)++;



    /* psivt clauses.
     */

    for ( vt = t->psi_VT[i]->next; vt; vt = vt->next ) {
      /* first: (-vt or (x=c)) for each (x=c)(vt)
       *
       * count num of (x=c) as side effect.
       */
      num = 0;
      for ( j = 0; j < gnum_relevant_fluents; j++ ) {
	if ( !vt->have[j] ) {
	  continue;
	}
	clause = new_CNF();
	clause->CNFid = ( int * ) calloc(2, sizeof( int ) );
	clause->sign = ( Bool * ) calloc(2, sizeof( Bool ) );
	clause->num = 2;
	clause->CNFid[0] = vt->CNFid;
	clause->sign[0] = FALSE;
	/* have to find the var value first.
	 */
	for ( v = t->V[j]->next; v; v = v->next ) {
	  if ( v->v == vt->vt[j] ) {
	    break;
	  }
	}
	if ( !v ) {
	  printf("\ndidn't find right v for vt(psi)?\n\n");
	  exit( 1 );
	}
	clause->CNFid[1] = v->CNFid;
	clause->sign[1] = TRUE;
	clause->prev = *cnfend;
	(*cnfend)->next = clause;
	*cnfend = clause;
	(*numclauses)++;
	num++;
      }
	
      /* now: ((OR_(x=c)(vt) -(x=c)) or vt)
       */
      clause = new_CNF();
      clause->CNFid = ( int * ) calloc(num+1, sizeof( int ) );
      clause->sign = ( Bool * ) calloc(num+1, sizeof( Bool ) );
      clause->num = num+1;
      num = 0;
      for ( j = 0; j < gnum_relevant_fluents; j++ ) {
	if ( !vt->have[j] ) {
	  continue;
	}
	/* INEFFICIENT! could remember this from above. probably benign:
	 * tuples haven't many members.
	 */
	for ( v = t->V[j]->next; v; v = v->next ) {
	  if ( v->v == vt->vt[j] ) {
	    break;
	  }
	}
	if ( !v ) {
	  printf("\ndidn't find right v for vt(psi)?\n\n");
	  exit( 1 );
	}
	clause->CNFid[num] = v->CNFid;
	clause->sign[num] = FALSE;
	num++;
      }
      clause->CNFid[num] = vt->CNFid;
      clause->sign[num] = TRUE;
      clause->prev = *cnfend;
      (*cnfend)->next = clause;
      *cnfend = clause;
      (*numclauses)++;
    } /* endfor vt over satisfying value tuples */
  } /* endfor i over psis indices */

}

  

void CNF_get_pre_con(RPGlayer *t, 
		     CNF **cnfend, 
		     int *numclauses)

{

  CNF *clause;
  
  RPGaction *a;
  RPGeffect *e;
  RPGfact *p;

  int i;



  for ( a = t->A->next; a; a = a->next ) {
    /* pre clauses for a: facts -- (-a or p)
     */
    for ( i = 0; i < a->a->num_preconds; i++ ) {
      clause = new_CNF();
      clause->CNFid = ( int * ) calloc(2, sizeof( int ) );
      clause->sign = ( Bool * ) calloc(2, sizeof( Bool ) );
      clause->num = 2;
      clause->CNFid[0] = a->CNFid;
      clause->sign[0] = FALSE;
      /* find the fact node and CNFid.
       * INEFFICIENT! might be better to organize facts
       * like fluents, as an indexed array.
       */
      for ( p = t->P->next; p; p = p->next ) {
	if ( p->id == a->a->preconds[i] ) {
	  break;
	}
      }
      if ( !p ) {
	printf("\ncan't find precond in pre clause?\n\n");
	exit( 1 );
      }
      clause->CNFid[1] = p->CNFid;
      clause->sign[1] = TRUE;      
      clause->prev = *cnfend;
      (*cnfend)->next = clause;
      *cnfend = clause;
      (*numclauses)++;
    }
    /* a->a means to chain from RPG a node to 
     * Action *a, ie the action description.
     */
    if ( gcmd_line.CNFencoding == 0 ) {
      for ( i = 0; i < a->a->num_numeric_preconds; i++ ) {
	/* pre clauses for a: (-a or constraint)
	 */
	clause = new_CNF();
	clause->CNFid = ( int * ) calloc(2, sizeof( int ) );
	clause->sign = ( Bool * ) calloc(2, sizeof( Bool ) );
	clause->num = 2;
	clause->CNFid[0] = a->CNFid;
	clause->sign[0] = FALSE;
	if ( t->constraint_CNFid[a->a->pre_constraint_id[i]] == -1 ) {
	  printf("\nprecond constraint not CNFid'ed?\n\n");
	  exit( 1 );
	}
	clause->CNFid[1] = t->constraint_CNFid[a->a->pre_constraint_id[i]];
	clause->sign[1] = TRUE;      
	clause->prev = *cnfend;
	(*cnfend)->next = clause;
	*cnfend = clause;
	(*numclauses)++;
      }
    }
    if ( gcmd_line.CNFencoding == 1 ) {
      if ( a->a->pre_psi_id != -1 ) {
	/* pre clauses for a: psi -- (-a or psi)
	 */
	clause = new_CNF();
	clause->CNFid = ( int * ) calloc(2, sizeof( int ) );
	clause->sign = ( Bool * ) calloc(2, sizeof( Bool ) );
	clause->num = 2;
	clause->CNFid[0] = a->CNFid;
	clause->sign[0] = FALSE;
	if ( t->psi_CNFid[a->a->pre_psi_id] == -1 ) {
	  printf("\nprecond psi not CNFid'ed?\n\n");
	  exit( 1 );
	}
	clause->CNFid[1] = t->psi_CNFid[a->a->pre_psi_id];
	clause->sign[1] = TRUE;      
	clause->prev = *cnfend;
	(*cnfend)->next = clause;
	*cnfend = clause;
	(*numclauses)++;
      }
    }


    
    /* con clauses for all e
     */
    for ( e = a->E->next; e; e = e->next ) {
      /* facts -- (-e or p)
       */
      for ( i = 0; i < e->e->num_conditions; i++ ) {
	clause = new_CNF();
	clause->CNFid = ( int * ) calloc(2, sizeof( int ) );
	clause->sign = ( Bool * ) calloc(2, sizeof( Bool ) );
	clause->num = 2;
	clause->CNFid[0] = e->CNFid;
	clause->sign[0] = FALSE;
	for ( p = t->P->next; p; p = p->next ) {
	  if ( p->id == e->e->conditions[i] ) {
	    break;
	  }
	}
	if ( !p ) {
	  printf("\ncan't find condition in con clause?\n\n");
	  exit( 1 );
	}
	clause->CNFid[1] = p->CNFid;
	clause->sign[1] = TRUE;      
	clause->prev = *cnfend;
	(*cnfend)->next = clause;
	*cnfend = clause;
	(*numclauses)++;
      }
      if ( gcmd_line.CNFencoding == 0 ) {
	for ( i = 0; i < e->e->num_numeric_conditions; i++ ) {
	  /* (-e or constraint)
	   */
	  clause = new_CNF();
	  clause->CNFid = ( int * ) calloc(2, sizeof( int ) );
	  clause->sign = ( Bool * ) calloc(2, sizeof( Bool ) );
	  clause->num = 2;
	  clause->CNFid[0] = e->CNFid;
	  clause->sign[0] = FALSE;
	  if ( t->constraint_CNFid[e->e->con_constraint_id[i]] == -1 ) {
	    printf("\ncondition constraint not CNFid'ed?\n\n");
	    exit( 1 );
	  }
	  clause->CNFid[1] = t->constraint_CNFid[e->e->con_constraint_id[i]];
	  clause->sign[1] = TRUE;      
	  clause->prev = *cnfend;
	  (*cnfend)->next = clause;
	  *cnfend = clause;
	  (*numclauses)++;
	}
      }
      if ( gcmd_line.CNFencoding == 1 ) {
	/* e->e: like for a->a above.
	 * only insert this if the con is actually different from the pre:
	 * remember that the num con is the result of conjoining the
	 * numeric pre with the numeric con.
	 */
	if ( e->e->con_psi_id != -1 &&
	     e->e->con_psi_id != a->a->pre_psi_id ) {
	  /* psi -- (-e or psi)
	   */
	  clause = new_CNF();
	  clause->CNFid = ( int * ) calloc(2, sizeof( int ) );
	  clause->sign = ( Bool * ) calloc(2, sizeof( Bool ) );
	  clause->num = 2;
	  clause->CNFid[0] = e->CNFid;
	  clause->sign[0] = FALSE;
	  if ( t->psi_CNFid[e->e->con_psi_id] == -1 ) {
	    printf("\ncondition psi not CNFid'ed?\n\n");
	    exit( 1 );
	  }
	  clause->CNFid[1] = t->psi_CNFid[e->e->con_psi_id];
	  clause->sign[1] = TRUE;      
	  clause->prev = *cnfend;
	  (*cnfend)->next = clause;
	  *cnfend = clause;
	  (*numclauses)++;
	}
      }
    } /* endfor e over a->E */
  } /* endfor a over t->A */

}



void CNF_get_ea_ae(RPGlayer *t, 
		   CNF **cnfend, 
		   int *numclauses)

{

  CNF *clause;
  
  RPGaction *a;
  RPGeffect *e;
  RPGfact *p;

  int i, num;



  /* for all e: (-e or a(e))
   */
  for ( a = t->A->next; a; a = a->next ) {
    for ( e = a->E->next; e; e = e->next ) {
      clause = new_CNF();
      clause->CNFid = ( int * ) calloc(2, sizeof( int ) );
      clause->sign = ( Bool * ) calloc(2, sizeof( Bool ) );
      clause->num = 2;
      clause->CNFid[0] = e->CNFid;
      clause->sign[0] = FALSE;
      clause->CNFid[1] = a->CNFid;
      clause->sign[1] = TRUE;      
      clause->prev = *cnfend;
      (*cnfend)->next = clause;
      *cnfend = clause;
      (*numclauses)++;
    }
  }



  /* for all a, e in E(a): (-a or OR{-z | z in con(e)} or e)
   */
  for ( a = t->A->next; a; a = a->next ) {
    for ( e = a->E->next; e; e = e->next ) {
      if ( gcmd_line.CNFencoding == 0 ) {
	num = 2 + e->e->num_conditions + e->e->num_numeric_conditions;/* a, e, con */
	clause = new_CNF();
	clause->CNFid = ( int * ) calloc(num, sizeof( int ) );
	clause->sign = ( Bool * ) calloc(num, sizeof( Bool ) );
	clause->num = num;
	clause->CNFid[0] = a->CNFid;
	clause->sign[0] = FALSE;
	num = 1;
	for ( i = 0; i < e->e->num_conditions; i++ ) {
	  for ( p = t->P->next; p; p = p->next ) {
	    if ( p->id == e->e->conditions[i] ) {
	      break;
	    }
	  }
	  if ( !p ) {
	    printf("\ncan't find condition in ae clause?\n\n");
	    exit( 1 );
	  }
	  clause->CNFid[num] = p->CNFid;
	  clause->sign[num] = FALSE;
	  num++;
	}
	for ( i = 0; i < e->e->num_numeric_conditions; i++ ) {
	  if ( t->constraint_CNFid[e->e->con_constraint_id[i]] == -1 ) {
	    printf("\ncondition constraint not CNFid'ed?\n\n");
	    exit( 1 );
	  }
	  clause->CNFid[num] = t->constraint_CNFid[e->e->con_constraint_id[i]];
	  clause->sign[num] = FALSE;      
	  num++;
	}
	clause->CNFid[num] = e->CNFid;
	clause->sign[num] = TRUE;
	clause->prev = *cnfend;
	(*cnfend)->next = clause;
	*cnfend = clause;
	(*numclauses)++;
      } /* endif CNF constraint encoding */
      if ( gcmd_line.CNFencoding == 1 ) {
	num = 2 + e->e->num_conditions;/* a, e, prop con */
	/* again, insert the numeric con here only if
	 * it is actually non-zero, ie the conjunction of
	 * pre+con is not equal to pre.
	 * (the prop con is NOT conjoined with the pre)
	 */
	if ( e->e->con_psi_id != -1 &&
	     e->e->con_psi_id != a->a->pre_psi_id ) {
	  num++;/* num con */
	}
	clause = new_CNF();
	clause->CNFid = ( int * ) calloc(num, sizeof( int ) );
	clause->sign = ( Bool * ) calloc(num, sizeof( Bool ) );
	clause->num = num;
	clause->CNFid[0] = a->CNFid;
	clause->sign[0] = FALSE;
	num = 1;
	for ( i = 0; i < e->e->num_conditions; i++ ) {
	  for ( p = t->P->next; p; p = p->next ) {
	    if ( p->id == e->e->conditions[i] ) {
	      break;
	    }
	  }
	  if ( !p ) {
	    printf("\ncan't find condition in ae clause?\n\n");
	    exit( 1 );
	  }
	  clause->CNFid[num] = p->CNFid;
	  clause->sign[num] = FALSE;
	  num++;
	}
	if ( e->e->con_psi_id != -1 &&
	     e->e->con_psi_id != a->a->pre_psi_id ) {
	  if ( t->psi_CNFid[e->e->con_psi_id] == -1 ) {
	    printf("\ncondition psi not CNFid'ed?\n\n");
	    exit( 1 );
	  }
	  clause->CNFid[num] = t->psi_CNFid[e->e->con_psi_id];
	  clause->sign[num] = FALSE;      
	  num++;
	}
	clause->CNFid[num] = e->CNFid;
	clause->sign[num] = TRUE;
	clause->prev = *cnfend;
	(*cnfend)->next = clause;
	*cnfend = clause;
	(*numclauses)++;
      } /* endif CNF psi encoding */
    } /* endfor e over effects */
  } /* endfor a over actions */

}



void CNF_get_eff(RPGlayer *t, 
		 CNF **cnfend, 
		 int *numclauses)

{

  /* this stuff is like in RPG_insert_effect, RPG.c
   */
  static ExpNode *exp, *lhsnode;
  static Bool fc = TRUE;

  CNF *clause;
  
  RPGaction *a;
  RPGeffect *e;
  RPGfact *p;
  RPGvaluetuple *jvt;
  RPGvalue *v, *jv;
  RPGlayer *tpp = t->next;

  int i, j, l, num;



  if ( fc ) {
    exp = new_ExpNode( FHEAD );
    lhsnode = new_ExpNode( FHEAD );
    exp->leftson = lhsnode;
    fc = FALSE;
  }



  for ( a = t->A->next; a; a = a->next ) {
    for ( e = a->E->next; e; e = e->next ) {

      /* for all e, add p: (-e_t or p_tpp)
       * for all e, del p: (-e_t or -p_tpp)
       */
      for ( i = 0; i < e->e->num_adds; i++ ) {
	for ( p = tpp->P->next; p; p = p->next ) {
	  if ( p->id == e->e->adds[i] ) {
	    break;
	  }
	}
	if ( !p ) {
	  printf("\ncan't find add in eff clause?\n\n");
	  exit( 1 );
	}
	clause = new_CNF();
	clause->CNFid = ( int * ) calloc(2, sizeof( int ) );
	clause->sign = ( Bool * ) calloc(2, sizeof( Bool ) );
	clause->num = 2;
	clause->CNFid[0] = e->CNFid;
	clause->sign[0] = FALSE;
	clause->CNFid[1] = p->CNFid;
	clause->sign[1] = TRUE;      
	clause->prev = *cnfend;
	(*cnfend)->next = clause;
	*cnfend = clause;
	(*numclauses)++;
      }
      for ( i = 0; i < e->e->num_dels; i++ ) {
	for ( p = tpp->P->next; p; p = p->next ) {
	  if ( p->id == e->e->dels[i] ) {
	    break;
	  }
	}
	if ( !p ) {
	  /* this may well happen... just means that this del cannot
	   * yet be true anyway...
	   */
	  continue;
/* 	  printf("\ncan't find del in eff clause?\n\n"); */
/* 	  exit( 1 ); */
	}
	clause = new_CNF();
	clause->CNFid = ( int * ) calloc(2, sizeof( int ) );
	clause->sign = ( Bool * ) calloc(2, sizeof( Bool ) );
	clause->num = 2;
	clause->CNFid[0] = e->CNFid;
	clause->sign[0] = FALSE;
	clause->CNFid[1] = p->CNFid;
	clause->sign[1] = FALSE;      
	clause->prev = *cnfend;
	(*cnfend)->next = clause;
	*cnfend = clause;
	(*numclauses)++;
      }



      /* the numeric stuff is more complicated:
       * for x := exp(barx), we gotta find all instantiations
       * pf barx that are in agreement with at least one
       * tuple satisfying the condition psi.
       * conveniently, there's the fn
       * RPG_get_valuetuples_exp in RPGvaluetuples.c
       * that does exactly what we need: given a psi id 
       * a layer and an exp(barx), it gives us all
       * barx tuples barc and values exp(barc) that agree
       * with the psi tuples.
       * what we gotta do is, pre-normalize the num effects
       * so they actually take the form x := exp(barx).
       */
      for ( i = 0; i < e->e->num_numeric_effects; i++ ) {
	/* normalize the expression.
	 */
	switch ( e->e->numeric_effects_neft[i] ) {
	case SCALE_UP:
	  lhsnode->fl = e->e->numeric_effects_fl[i];
	  exp->connective = MU;
	  exp->rightson = e->e->numeric_effects_rh[i];
	  break;
	case SCALE_DOWN:
	  lhsnode->fl = e->e->numeric_effects_fl[i];
	  exp->connective = DI;
	  exp->rightson = e->e->numeric_effects_rh[i];
	  break;
	case INCREASE:
	  lhsnode->fl = e->e->numeric_effects_fl[i];
	  exp->connective = AD;
	  exp->rightson = e->e->numeric_effects_rh[i];
	  break;
	case DECREASE:
	  lhsnode->fl = e->e->numeric_effects_fl[i];
	  exp->connective = SU;
	  exp->rightson = e->e->numeric_effects_rh[i];
	  break;
	case ASSIGN:
	  /* here, the rhs actually is the expression we're looking for.
	   */
	  break;
	default:
	  printf("\nillegal numeric effect type!\n\n");
	  exit( 1 );
	}

	/* call RPG_get_valuetuples_exp to obtain the tuples and values.
	 * NOTE: the psi id may be -1, in which case the fn will just assume
	 * a single complete "don't care" tuple as the psi-tuple list
	 * to match against.
	 */
	if ( e->e->numeric_effects_neft[i] != ASSIGN ) {
	  RPG_get_valuetuples_exp(t, e->e->con_psi_id, exp);
	} else {
	  RPG_get_valuetuples_exp(t, e->e->con_psi_id, e->e->numeric_effects_rh[i]);
	}

	/* now collect the results and form the clauses.
	 * jvt will range over the barc, and synchronously jv will
	 * range over the c.
	 */
	jvt = gget_valuetuples_exp_result_vt->next;
	jv = gget_valuetuples_exp_result_v->next;
	for ( j = 0; j < gget_valuetuples_exp_num_result; j++ ) {
	  /* effect has form x := exp(barx);
	   * for each valuetuple barc and result value c,
	   * we get the clause (-e_t or OR{-(xi=ci)_t | (xi=ci) in barc} or (x=c)_tpp)
	   */

	  /* first count how many literals we'll have.
	   */
	  num = 0;
	  for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	    if ( jvt->have[l] ) {
	      num++;
	    }
	  }
	  
	  /* get the clause!
	   */
	  clause = new_CNF();
	  clause->CNFid = ( int * ) calloc(num+2, sizeof( int ) );
	  clause->sign = ( Bool * ) calloc(num+2, sizeof( Bool ) );
	  clause->num = num+2;
	  clause->CNFid[0] = e->CNFid;
	  clause->sign[0] = FALSE;
	  num = 1;
	  for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	    if ( !jvt->have[l] ) {
	      continue;
	    }
	    /* have to look this value up...
	     * INEFFICIENT! maybe just store the value pointer
	     * in the tuple, instead of the value itself?
	     */
	    for ( v = t->V[l]->next; v; v = v->next ) {
	      if ( v->v == jvt->vt[l] ) {
		break;
	      }
	    }
	    if ( !v ) {
	      printf("\ndidn't find instantiation value in eff clause exp?\n\n");
	      exit( 1 );
	    }
	    clause->CNFid[num] = v->CNFid;
	    clause->sign[num] = FALSE;
	    num++;
	  }
	  /* also have to look the result value up - in tpp!
	   * INEFFICIENT! see above.
	   */
	  for ( v = tpp->V[e->e->numeric_effects_fl[i]]->next; v; v = v->next ) {
	    if ( v->v == jv->v ) {
	      break;
	    }
	  }
	  if ( !v ) {
	    printf("\ndidn't find instantiation value in eff clause exp?\n\n");
	    exit( 1 );
	  }
	  clause->CNFid[num] = v->CNFid;
	  clause->sign[num] = TRUE;
	  clause->prev = *cnfend;
	  (*cnfend)->next = clause;
	  *cnfend = clause;
	  (*numclauses)++;

	  jvt = jvt->next;
	  jv = jv->next;
	} /* endfor jvt, jv, j over RPG_get_valuetuples_exp output */
      } /* endfor i over numeric effects */
    } /* endfor e over effects */
  } /* endfor a over actions */

}



void CNF_get_frame(RPGlayer *t, 
		   CNF **cnfend, 
		   int *numclauses)

{

  CNF *clause;
  
  RPGfact *p, *ptpp;
  RPGvalue *v, *vtpp;
  RPGlayer *tpp = t->next;

  RPGeffectlist *el;

  int i, num;

  

  /* fact frame clauses:
   * all p in P_t: 
   *     positive: (-p_t or OR{e_t | p in del(e)} or p_tpp)
   *     negative: (p_t or OR{e_t | p in add(e)} or -p_tpp)
   * all p not in P_t, p in P_tpp: 
   *     negative2: (OR{e_t | p in add(e)} or -p_tpp)
   *
   * (read as implications: if p is true at t and not deleted, it is true at tpp)
   */
  for ( p = t->P->next; p; p = p->next ) {

    /* first the positive frame clause
     */
    num = 0;
    for ( el = t->tD[p->id]->next; el; el = el->next ) {
      num++;
    }
    clause = new_CNF();
    clause->CNFid = ( int * ) calloc(num+2, sizeof( int ) );
    clause->sign = ( Bool * ) calloc(num+2, sizeof( Bool ) );
    clause->num = num+2;
    clause->CNFid[0] = p->CNFid;
    clause->sign[0] = FALSE;
    num = 1;
    for ( el = t->tD[p->id]->next; el; el = el->next ) {
      clause->CNFid[num] = el->e->CNFid;
      clause->sign[num] = TRUE;
      num++;
    }
    /* find p_tpp
     */
    for ( ptpp = tpp->P->next; ptpp; ptpp = ptpp->next ) {
      if ( ptpp->id == p->id ) {
	break;
      }
    }
    if ( !ptpp ) {
      printf("\ncan't find ptpp in frame clause?\n\n");
      exit( 1 );
    }
    clause->CNFid[num] = ptpp->CNFid;
    clause->sign[num] = TRUE;
    (*cnfend)->next = clause;
    *cnfend = clause;
    (*numclauses)++;

    /* now the negative frame clause
     */
    num = 0;
    for ( el = t->tA[p->id]->next; el; el = el->next ) {
      num++;
    }
    clause = new_CNF();
    clause->CNFid = ( int * ) calloc(num+2, sizeof( int ) );
    clause->sign = ( Bool * ) calloc(num+2, sizeof( Bool ) );
    clause->num = num+2;
    clause->CNFid[0] = p->CNFid;
    clause->sign[0] = TRUE;
    num = 1;
    for ( el = t->tA[p->id]->next; el; el = el->next ) {
      clause->CNFid[num] = el->e->CNFid;
      clause->sign[num] = TRUE;
      num++;
    }
    /* we still got p_tpp from above.
     */
    clause->CNFid[num] = ptpp->CNFid;
    clause->sign[num] = FALSE;
    (*cnfend)->next = clause;
    *cnfend = clause;
    (*numclauses)++;
  } /* endfor p over P_t */

  /* and now for the negative2 stuff:
   */
  for ( ptpp = tpp->P->next; ptpp; ptpp = ptpp->next ) {
    /* only those that aren't in t.
     */
    if ( t->is_P[ptpp->id] ) {
      continue;
    }
    num = 0;
    for ( el = t->tA[ptpp->id]->next; el; el = el->next ) {
      num++;
    }
    clause = new_CNF();
    clause->CNFid = ( int * ) calloc(num+1, sizeof( int ) );
    clause->sign = ( Bool * ) calloc(num+1, sizeof( Bool ) );
    clause->num = num+1;
    num = 0;
    for ( el = t->tA[ptpp->id]->next; el; el = el->next ) {
      clause->CNFid[num] = el->e->CNFid;
      clause->sign[num] = TRUE;
      num++;
    }
    clause->CNFid[num] = ptpp->CNFid;
    clause->sign[num] = FALSE;
    (*cnfend)->next = clause;
    *cnfend = clause;
    (*numclauses)++;
  }



  /* fluent frame clauses:
   * for all fluents x and values c of x at t:
   *     positive: (-(x=c)_t or OR{e_t | (x:=exp) in e} or (x=c)_tpp)
   *     negative: ((x=c)_t or OR{e_t | (x:=exp) in e} or -(x=c)_tpp)
   * for all fluents x and values c of x at tpp that aren't values c of x at t:
   *     negative2: (OR{e_t | (x:=exp) in e} or -(x=c)_tpp)
   */
  for ( i = 0; i < gnum_relevant_fluents; i++ ) {
    for ( v = t->V[i]->next; v; v = v->next ) {

      /* first the positive frame clause
       */
      num = 0;
      for ( el = t->tXA[i]->next; el; el = el->next ) {
	num++;
      }
      clause = new_CNF();
      clause->CNFid = ( int * ) calloc(num+2, sizeof( int ) );
      clause->sign = ( Bool * ) calloc(num+2, sizeof( Bool ) );
      clause->num = num+2;
      clause->CNFid[0] = v->CNFid;
      clause->sign[0] = FALSE;
      num = 1;
      for ( el = t->tXA[i]->next; el; el = el->next ) {
	clause->CNFid[num] = el->e->CNFid;
	clause->sign[num] = TRUE;
	num++;
      }
      /* find v_tpp
       */
      for ( vtpp = tpp->V[i]->next; vtpp; vtpp = vtpp->next ) {
	if ( vtpp->v == v->v ) {
	  break;
	}
      }
      if ( !vtpp ) {
	printf("\ncan't find vtpp in frame clause?\n\n");
	exit( 1 );
      }
      clause->CNFid[num] = vtpp->CNFid;
      clause->sign[num] = TRUE;
      (*cnfend)->next = clause;
      *cnfend = clause;
      (*numclauses)++;

      /* now the negative frame clause
       */

      /* we still have the number from above, namely #effs = num-1!
       */
      clause = new_CNF();
      clause->CNFid = ( int * ) calloc(num+1, sizeof( int ) );
      clause->sign = ( Bool * ) calloc(num+1, sizeof( Bool ) );
      clause->num = num+1;
      clause->CNFid[0] = v->CNFid;
      clause->sign[0] = TRUE;
      num = 1;
      for ( el = t->tXA[i]->next; el; el = el->next ) {
	clause->CNFid[num] = el->e->CNFid;
	clause->sign[num] = TRUE;
	num++;
      }
      /* we still have v_tpp from above!
       */
      clause->CNFid[num] = vtpp->CNFid;
      clause->sign[num] = FALSE;
      (*cnfend)->next = clause;
      *cnfend = clause;
      (*numclauses)++;
    } /* endfor v over values at t */
  } /* endfor i over fluent indices */

  /* and now for the negative2 stuff:
   */
  for ( i = 0; i < gnum_relevant_fluents; i++ ) {
    for ( vtpp = tpp->V[i]->next; vtpp; vtpp = vtpp->next ) {
      /* only those that aren't in t.
       *
       * INEFFICIENT: e.g. we could remember this from above.
       */
      for ( v = t->V[i]->next; v; v = v->next ) {
	if ( v->v == vtpp->v ) {
	  break;
	}
      }
      if ( v ) {
	continue;
      }
      num = 0;
      for ( el = t->tXA[i]->next; el; el = el->next ) {
	num++;
      }
      clause = new_CNF();
      clause->CNFid = ( int * ) calloc(num+1, sizeof( int ) );
      clause->sign = ( Bool * ) calloc(num+1, sizeof( Bool ) );
      clause->num = num+1;
      num = 0;
      for ( el = t->tXA[i]->next; el; el = el->next ) {
	clause->CNFid[num] = el->e->CNFid;
	clause->sign[num] = TRUE;
	num++;
      }
      clause->CNFid[num] = vtpp->CNFid;
      clause->sign[num] = FALSE;
      (*cnfend)->next = clause;
      *cnfend = clause;
      (*numclauses)++;
    } /* endfor vtpp over values at tpp */
  } /* endfor i over fluent indices */

}

Bool ignore_mutex = FALSE;

void CNF_get_vmutex(RPGlayer *t, 
		    CNF **cnfend, 
		    int *numclauses)

{

  CNF *clause;
  
  RPGvalue *iv, *jv;

  int i;



  /* (-(x=c) or -(x=c'))
   */
  for ( i = 0; i < gnum_relevant_fluents; i++ ) {
    if ( !t->V[i]->next /* 0 values */ ||
	 !t->V[i]->next->next /* 1 value */ ) {
      continue;
    }
    if( ignore_mutex )
      continue;
    for ( iv = t->V[i]->next; iv->next; iv = iv->next ) {
      for ( jv = iv->next; jv; jv = jv->next ) {
	clause = new_CNF();
	clause->CNFid = ( int * ) calloc(2, sizeof( int ) );
	clause->sign = ( Bool * ) calloc(2, sizeof( Bool ) );
	clause->num = 2;
	clause->CNFid[0] = iv->CNFid;
	clause->sign[0] = FALSE;
	clause->CNFid[1] = jv->CNFid;
	clause->sign[1] = FALSE;      
	clause->prev = *cnfend;
	(*cnfend)->next = clause;
	*cnfend = clause;
	(*numclauses)++;
      } /* endfor iv over values from iv->next to last */
    } /* endfor iv over values at t except last */
  } /* endfor i over fluent indices */

}



/* (-a or -e) for all a not| e
 * either e dels a pre of a, or e affects an x mentioned in a's numpre.
 */
void CNF_get_aemutex(RPGlayer *t, 
		     CNF **cnfend, 
		     int *numclauses)

{

  /* to avoid duplicates
   */
  static Bool fc = TRUE;
  static Bool **had;

  CNF *clause;
  
  RPGeffect *e;

  RPGactionlist *al;
  RPGeffectlist *el;

  int i, j;



  if ( fc ) {
    had = ( Bool ** ) calloc(gnum_actions, sizeof( Bool * ));
    for ( i = 0; i < gnum_actions; i++ ) {
      had[i] = ( Bool * ) calloc(gnum_effects, sizeof( Bool * ));
    }    
    fc = FALSE;
  }



  /* initialize duplicate table.
   * INEFFICIENT: could remember and undo changes instead.
   */
  for ( i = 0; i < gnum_actions; i++ ) {
    for ( j = 0; j < gnum_effects; j++ ) {
      had[i][j] = FALSE;
    }
  }



  /* all facts that could be conflicted upon
   */
  for ( i = 0; i < gnum_relevant_facts; i++ ) {
    /* just get all conflicting action/effect pairs.
     */
    for ( al = t->tP[i]->next; al; al = al->next ) {
      for ( el = t->tD[i]->next; el; el = el->next ) {
	/* chain list a/e -> RPG a/e -> real a/e -> id
	 */
	if ( had[al->a->a->id][el->e->e->id] ) {
	  continue;
	}
	/* skip the pair of e is an effect of a!
	 * INEFFICIENT! better have a pointer from the
	 * effects back to the actions.
	 */
	for ( e = al->a->E->next; e; e = e->next ) {
	  if ( e == el->e ) break;
	}
	if ( e ) {
	  continue;
	}
	if( ignore_mutex )
	  continue;
	if( ignore_this_mutex( t, al->a->CNFid, el->e->CNFid) )
	  continue;
	had[al->a->a->id][el->e->e->id] = TRUE;
	clause = new_CNF();
	clause->CNFid = ( int * ) calloc(2, sizeof( int ) );
	clause->sign = ( Bool * ) calloc(2, sizeof( Bool ) );
	clause->num = 2;
	clause->CNFid[0] = al->a->CNFid;
	clause->sign[0] = FALSE;
	clause->CNFid[1] = el->e->CNFid;
	clause->sign[1] = FALSE;      
	clause->prev = *cnfend;
	(*cnfend)->next = clause;
	*cnfend = clause;
	(*numclauses)++;
      }
    }
  }

  /* all fluents that could be conflicted upon
   */
  for ( i = 0; i < gnum_relevant_fluents; i++ ) {
    /* just get all conflicting action/effect pairs.
     */
    for ( al = t->tXP[i]->next; al; al = al->next ) {
      for ( el = t->tXA[i]->next; el; el = el->next ) {
	if ( had[al->a->a->id][el->e->e->id] ) {
	  continue;
	}
	for ( e = al->a->E->next; e; e = e->next ) {
	  if ( e == el->e ) break;
	}
	if ( e ) {
	  continue;
	}
	if( ignore_mutex )
	  continue;
	if( ignore_this_mutex( t, al->a->CNFid, el->e->CNFid) )
	  continue;
	had[al->a->a->id][el->e->e->id] = TRUE;
	clause = new_CNF();
	clause->CNFid = ( int * ) calloc(2, sizeof( int ) );
	clause->sign = ( Bool * ) calloc(2, sizeof( Bool ) );
	clause->num = 2;
	clause->CNFid[0] = al->a->CNFid;
	clause->sign[0] = FALSE;
	clause->CNFid[1] = el->e->CNFid;
	clause->sign[1] = FALSE;      
	clause->prev = *cnfend;
	(*cnfend)->next = clause;
	*cnfend = clause;
	(*numclauses)++;
      }
    }
  }

}



/* (-e or -e') for all e not| e'
 * either:
 *       e dels a (con or add) of e' (or vive versa)
 *       e affects an x mentioned by con or effrhs of e' (or vice versa)
 *       e and e' affect the same x.
 */
void CNF_get_eemutex(RPGlayer *t, 
		     CNF **cnfend, 
		     int *numclauses)

{

  /* to avoid duplicates
   */
  static Bool fc = TRUE;
  static Bool **had;

  CNF *clause;
  
  RPGeffectlist *el1, *el2;
  RPGaction *a;
  RPGeffect *e;

  int i, j;
  Bool had1, had2;



  if ( fc ) {
    had = ( Bool ** ) calloc(gnum_effects, sizeof( Bool * ));
    for ( i = 0; i < gnum_effects; i++ ) {
      had[i] = ( Bool * ) calloc(gnum_effects, sizeof( Bool * ));
    }    
    fc = FALSE;
  }



  /* initialize duplicate table.
   * INEFFICIENT: could remember and undo changes instead.
   */
  for ( i = 0; i < gnum_effects; i++ ) {
    for ( j = 0; j < gnum_effects; j++ ) {
      had[i][j] = FALSE;
    }
  }



  /* all facts that could be conflicted upon
   */
  for ( i = 0; i < gnum_relevant_facts; i++ ) {
    /* con <-> del: just get all conflicting pairs.
     */
    for ( el1 = t->tC[i]->next; el1; el1 = el1->next ) {
      for ( el2 = t->tD[i]->next; el2; el2 = el2->next ) {
	if ( el1->e == el2->e ) {
	  continue;
	}
	/* chain list e -> RPG e -> real e -> id
	 */
	if ( had[el1->e->e->id][el2->e->e->id] ) {
	  continue;
	}
	if( ignore_mutex )
	  continue;
	if( ignore_this_mutex( t, el1->e->CNFid, el2->e->CNFid ) )
	  continue;
	had[el1->e->e->id][el2->e->e->id] = TRUE;
	clause = new_CNF();
	clause->CNFid = ( int * ) calloc(2, sizeof( int ) );
	clause->sign = ( Bool * ) calloc(2, sizeof( Bool ) );
	clause->num = 2;
	clause->CNFid[0] = el1->e->CNFid;
	clause->sign[0] = FALSE;
	clause->CNFid[1] = el2->e->CNFid;
	clause->sign[1] = FALSE;      
	clause->prev = *cnfend;
	(*cnfend)->next = clause;
	*cnfend = clause;
	(*numclauses)++;
      }
    }
 
    /* add <-> del: just get all conflicting pairs.
     */
    for ( el1 = t->tA[i]->next; el1; el1 = el1->next ) {
      for ( el2 = t->tD[i]->next; el2; el2 = el2->next ) {
	if ( el1->e == el2->e ) {
	  continue;
	}
	if ( had[el1->e->e->id][el2->e->e->id] ) {
	  continue;
	}
	if( ignore_mutex )
	  continue;
	if( ignore_this_mutex( t, el1->e->CNFid, el2->e->CNFid ) )
	  continue;
	had[el1->e->e->id][el2->e->e->id] = TRUE;
	clause = new_CNF();
	clause->CNFid = ( int * ) calloc(2, sizeof( int ) );
	clause->sign = ( Bool * ) calloc(2, sizeof( Bool ) );
	clause->num = 2;
	clause->CNFid[0] = el1->e->CNFid;
	clause->sign[0] = FALSE;
	clause->CNFid[1] = el2->e->CNFid;
	clause->sign[1] = FALSE;      
	clause->prev = *cnfend;
	(*cnfend)->next = clause;
	*cnfend = clause;
	(*numclauses)++;
      }
    }
  } /* endfor i over fact indices */



  /* all fluents that could be conflicted upon
   */
  for ( i = 0; i < gnum_relevant_fluents; i++ ) {
    /* con \cup effrhs <-> affect: just get all conflicting pairs.
     */
    for ( el1 = t->tXC[i]->next; el1; el1 = el1->next ) {
      for ( el2 = t->tXA[i]->next; el2; el2 = el2->next ) {
	if ( el1->e == el2->e ) {
	  continue;
	}
	/* check if they're effects of the same action!
	 * in that case, no problem: the effects will appear in parallel
	 * and not hurt each other.
	 *
	 * INEFFICIENT!!! why on earth does an effect not have a pointer to
	 * its action????
	 */
	for ( a = t->A->next; a; a = a->next ) {
	  had1 = FALSE;
	  had2 = FALSE;
	  for ( e = a->E->next; e; e = e->next ) {
	    if ( e == el1->e ) {
	      had1 = TRUE;
	    }
	    if ( e == el2->e ) {
	      had2 = TRUE;
	    }
	  }
	  if ( had1 && had2 ) {
	    break;
	  }
	}
	if ( a ) {
	  continue;
	}
	
	if ( had[el1->e->e->id][el2->e->e->id] ) {
	  continue;
	}
	if( ignore_mutex )
	  continue;
	if( ignore_this_mutex( t, el1->e->CNFid, el2->e->CNFid ) )
	  continue;
	had[el1->e->e->id][el2->e->e->id] = TRUE;
	clause = new_CNF();
	clause->CNFid = ( int * ) calloc(2, sizeof( int ) );
	clause->sign = ( Bool * ) calloc(2, sizeof( Bool ) );
	clause->num = 2;
	clause->CNFid[0] = el1->e->CNFid;
	clause->sign[0] = FALSE;
	clause->CNFid[1] = el2->e->CNFid;
	clause->sign[1] = FALSE;      
	clause->prev = *cnfend;
	(*cnfend)->next = clause;
	*cnfend = clause;
	(*numclauses)++;
      }
    }

    /* affect <-> affect: just get all conflicting pairs.
     */
    if ( !t->tXA[i]->next /* affected by no effect */ ||
	 !t->tXA[i]->next->next /* affected by just 1 effect */ ) {
      continue;
    }
    for ( el1 = t->tXA[i]->next; el1->next; el1 = el1->next ) {
      for ( el2 = el1->next; el2; el2 = el2->next ) {
	if ( el1->e == el2->e ) {
	  printf("\naffecter occurs twice in connectivity list XA?: at ee clauses\n\n");
	  exit( 1 );
	}


	
	/* NO! this here is fine, but we cannot model - at least not without major 
	 * adaptations -- the value that var i will have at tpp.
	 */
/* 	/\* PDDL2.1 level 2: check if both effects are in {increase, decrease};  */
/* 	 * if so, don't make them mutex. */
/* 	 *\/ */
/* 	/\* first have to find the effect on this fluent here. */
/* 	 *\/ */
/* 	for ( j = 0; j < el1->e->e->num_numeric_effects; j++ ) { */
/* 	  if ( el1->e->e->numeric_effects_fl[j] == i ) { */
/* 	    break; */
/* 	  } */
/* 	} */
/* 	if ( j == el1->e->e->num_numeric_effects ) { */
/* 	  printf("\ndidn't find affected fluent in ee clauses, el1?\n\n"); */
/* 	  exit( 1 ); */
/* 	} */
/* 	if ( el1->e->e->numeric_effects_neft[j] == INCREASE || */
/* 	     el1->e->e->numeric_effects_neft[j] == DECREASE ) { */
/* 	  /\* now check the other guy. */
/* 	   *\/ */
/* 	  for ( j = 0; j < el2->e->e->num_numeric_effects; j++ ) { */
/* 	    if ( el2->e->e->numeric_effects_fl[j] == i ) { */
/* 	      break; */
/* 	    } */
/* 	  } */
/* 	  if ( j == el2->e->e->num_numeric_effects ) { */
/* 	    printf("\ndidn't find affected fluent in ee clauses, el2?\n\n"); */
/* 	    exit( 1 ); */
/* 	  } */
/* 	  if ( el2->e->e->numeric_effects_neft[j] == INCREASE || */
/* 	       el2->e->e->numeric_effects_neft[j] == DECREASE ) { */
/* 	    /\* yes! both are "additive" (PDDL 2.1 level 2) */
/* 	     * allow them. */
/* 	     * note that the effect rhs exps are not affected by the other effect, */
/* 	     * or the effects will have been made mutex above already. */
/* 	     *\/ */
/* 	    continue; */
/* 	  } */
/* 	} */
	/* check if both effects are assign and rhs value is identical
	 * if so, don't make them mutex.
	 */
	/* first have to find the effect on this fluent here.
	 */
	for ( j = 0; j < el1->e->e->num_numeric_effects; j++ ) {
	  if ( el1->e->e->numeric_effects_fl[j] == i ) {
	    break;
	  }
	}
	if ( j == el1->e->e->num_numeric_effects ) {
	  printf("\ndidn't find affected fluent in ee clauses, el1?\n\n");
	  exit( 1 );
	}
	if ( el1->e->e->numeric_effects_neft[j] == ASSIGN ) {
	  /* now check the other guy.
	   */
	  for ( j = 0; j < el2->e->e->num_numeric_effects; j++ ) {
	    if ( el2->e->e->numeric_effects_fl[j] == i ) {
	      break;
	    }
	  }
	  if ( j == el2->e->e->num_numeric_effects ) {
	    printf("\ndidn't find affected fluent in ee clauses, el2?\n\n");
	    exit( 1 );
	  }
	  if ( el2->e->e->numeric_effects_neft[j] == ASSIGN ) {
	    /* just don't make them mutex, and leave the rest up to the
	     * eff clauses: if the values will be different, that'll cause
	     * a conflict.
	     */
	    continue;
	  }
	}



	if ( had[el1->e->e->id][el2->e->e->id] ) {
	  continue;
	}
	if( ignore_mutex )
	  continue;
	if( ignore_this_mutex( t, el1->e->CNFid, el2->e->CNFid ) )
	  continue;
	had[el1->e->e->id][el2->e->e->id] = TRUE;
	clause = new_CNF();
	clause->CNFid = ( int * ) calloc(2, sizeof( int ) );
	clause->sign = ( Bool * ) calloc(2, sizeof( Bool ) );
	clause->num = 2;
	clause->CNFid[0] = el1->e->CNFid;
	clause->sign[0] = FALSE;
	clause->CNFid[1] = el2->e->CNFid;
	clause->sign[1] = FALSE;      
	clause->prev = *cnfend;
	(*cnfend)->next = clause;
	*cnfend = clause;
	(*numclauses)++;
      }
    }
  } /* endfor i over fluent indices */

}




