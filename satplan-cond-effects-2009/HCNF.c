

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
 * File: HCNF.c
 * Description: functions for transforming fully-fledged RPG
 *              into a hybrid CNF.
 *
 * NOTE: we actually don't need the "fully-fledged" in here,
 *       it's just a by-product of comparing to CNF.
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

#include "HCNF.h"















/* Turns the fully-fledged numeric RPG into a hybrid CNF formula, as follows:
 *
 *
 * There are time steps t, of which the last, goalt, contains only facts p and
 * fluents x, not actions/effects. There are boolean variables for facts, actions,
 * and effects, at time steps. There are real-valued variables for fluents at time 
 * steps.
 *
 *
 * clauses:
 *
 *
 * init: for p in I: (p_0); for all x: (x_0=I(x))
 *
 * 
 * pre: for all t\goalt, a in A_t, z in pre(a): (-a_t or z_t) [z == fact p or z == (exp comp exp)]
 * con: for all t\goalt, e in E_t, z in con(e): (-e_t or z_t)
 *
 *
 * ea: for all t\goalt, e in E_t: (-e_t or a(e)_t)
 * ae: for all t\goalt, a in A_t, e in E(a) \cap E_t: (-a_t or OR{-z_t | z in con(e)} or e_t)
 *
 *
 * eff: for all t\goalt, e in E_t: f.a. p in add(e): (-e_t or p_{t+1})
 *                                 f.a. p in del(e): (-e_t or -p_{t+1})
 *                                 f.a. (x := exp) in e: (-e_t or (x_{t+1}=exp_t)
 *
 *
 * frame: for all t\goalt, p in P_t: (-p_t or OR{e_t | p in del(e)} or p_{t+1})
 *                                   (p_t or OR{e_t | p in add(e)} or -p_{t+1})
 *        for all t\goalt, p not in P_t, p in P_{t+1}:  (OR{e_t | p in add(e)} or -p_{t+1})
 *
 *        for all t\goalt, x: (OR{e_t | e affects x} or x_{t+1}=x_t)
 *
 *
 * goal: for all z in G: (z_{goalt})
 *
 * aemutex: for all t\goalt, a in A_t, e in E_t\E(a), a\not|e: (-a_t, -e_t)
 * eemutex: for all t\goalt, e1, e2 in E_t, e1\not|e2: (-e1_t, -e2_t)
 *
 *
 *
 * a\not|e :iff pre(a) \cap del(e) not empty, or pre(a) mentions x affected by e
 *
 * e1\not|e2 :iff 1. (con(e1) cup add(e1)) cap del(e2) not empty, or vice versa, or
 *                2. (con(e1) cup effect rhs exps e1) mention x affected by e2, or vv, or                
 *                3. an x is affected by both e1 and e2.
 *
 *
 * IF gcmd_line.CNFencoding == 3: 
 *     tvalue clauses: for all t, x: (OR{x_t=c | c in V(x)_t})
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





















/* this creates the initial clauses as specified
 * in the RPGlayer, appends them to the CNF end,
 * and sets the CNF end to the new end. updates nrs.
 */
void HCNF_initialize(RPGlayer *t, 
		     HCNF **cnfend,
		     int *numvars,
		     int *numclauses)

{

  HCNF *clause;
  
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
  /* all vars with at least one value.
   * first get space for the indices, and initialize.
   */
  t->x_CNFid = ( int * ) calloc(gnum_relevant_fluents, sizeof( int ));
  for ( i = 0; i < gnum_relevant_fluents; i++ ) {
    t->x_CNFid[i] = -1;
  }
  for ( i = 0; i < gnum_relevant_fluents; i++ ) {
    if ( !t->V[i]->next ) {
      /* happens for initially undefined fluents.
       */
      continue;
    }
    if ( t->x_CNFid[i] != -1 ) {
      printf("\ndouble setting CNFid fact?");
      exit( 1 );
    }
    t->x_CNFid[i] = CNFid++;
    /* at most one value in ini state!
     */
    if ( t->V[i]->next->next ) {
      printf("\nvar > 1 ini value?\n\n");
      exit( 1 );
    }
  }
  *numvars = CNFid-1;



  /* get the initial-fact clauses.
   */
  for ( p = t->P->next; p; p = p->next ) {
    clause = new_HCNF();
    clause->pCNFid = ( int * ) calloc(1, sizeof( int ) );
    clause->psign = ( Bool * ) calloc(1, sizeof( Bool ) );
    clause->pnum = 1;
    clause->pCNFid[0] = p->CNFid;
    clause->psign[0] = TRUE;
    clause->nnum = 0;
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
    clause = new_HCNF();
    clause->pnum = 0;
    clause->ncomp = ( Comparator * ) calloc(1, sizeof( Comparator ) );
    clause->nlhs = ( ExpNode_pointer * ) calloc(1, sizeof( ExpNode * ) );
    clause->nrhs = ( ExpNode_pointer * ) calloc(1, sizeof( ExpNode * ) );
    clause->nsign = ( Bool * ) calloc(1, sizeof( Bool ) );
    clause->nnum = 1;
    clause->ncomp[0] = EQ;
    clause->nlhs[0] = new_ExpNode(FHEAD);
    clause->nlhs[0]->CNFid = t->x_CNFid[i];
    clause->nrhs[0] = new_ExpNode(NUMBER);
    /* the first and only value in the list.
     */
    clause->nrhs[0]->value = t->V[i]->next->v;
    clause->nsign[0] = TRUE;
    clause->prev = *cnfend;
    (*cnfend)->next = clause;
    *cnfend = clause;
    (*numclauses)++;
  }

}



/* this creates the:
 *    pre, con clauses at t,
 *    ea, ae clauses at t,
 *    eff and frame clauses at t->t+1,
 *    action/effect mutex clauses at t.
 * appends to cnf end, updates cnf end. updates nrs.
 */
void HCNF_extend(RPGlayer *t, 
		 HCNF **cnfend,
		 int *numvars,
		 int *numclauses)

{

  RPGaction *a;
  RPGeffect *e;
  RPGfact *p;
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
  tpp->x_CNFid = ( int * ) calloc(gnum_relevant_fluents, sizeof( int ));
  for ( i = 0; i < gnum_relevant_fluents; i++ ) {
    tpp->x_CNFid[i] = -1;
  }
  for ( i = 0; i < gnum_relevant_fluents; i++ ) {
    if ( !tpp->V[i]->next ) {
      continue;
    }
    if ( tpp->x_CNFid[i] != -1 ) {
      printf("\ndouble setting CNFid tpp fluent?");
      exit( 1 );
    }
    tpp->x_CNFid[i] = CNFid++;
  }
  *numvars = CNFid-1;



  /* now for the clauses!
   *
   * order of these fn calls doesn't matter.
   */

  /* get the pre and con clauses at t.
   */
  HCNF_get_pre_con(t, cnfend, numclauses);

  /* get the ea and ae clauses at t.
   */
  HCNF_get_ea_ae(t, cnfend, numclauses);

  /* get the eff clauses at t -> tpp.
   */
  HCNF_get_eff(t, cnfend, numclauses);

  /* get the frame clauses at t -> tpp.
   */
  HCNF_get_frame(t, cnfend, numclauses);

  /* get the a/e mutex clauses at t.
   */
  HCNF_get_aemutex(t, cnfend, numclauses);

  /* get the e/e mutex clauses at t.
   */
  HCNF_get_eemutex(t, cnfend, numclauses);

  if ( gcmd_line.CNFencoding == 3 ) {
    /* insert additional information that we get from the RPG
     * -- this is "un-hybrid" and will work only based on our 
     * approach here. just to check what it does. 
     */
    HCNF_get_tvalue(tpp, cnfend, numclauses);
  }

}



/* this creates the goal clauses at t and appends them
 * to the HCNF. updates nr of clauses only since no new vars will
 * be added.
 */
void HCNF_get_goal(RPGlayer *t, 
		   HCNF **cnfend, 
		   int *numclauses)

{

  HCNF *clause;

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
    clause = new_HCNF();
    clause->pCNFid = ( int * ) calloc(1, sizeof( int ) );
    clause->psign = ( Bool * ) calloc(1, sizeof( Bool ) );
    clause->pnum = 1;
    clause->pCNFid[0] = p->CNFid;
    clause->psign[0] = TRUE;
    clause->nnum = 0;
    clause->prev = *cnfend;
    (*cnfend)->next = clause;
    *cnfend = clause;
    (*numclauses)++;
  }



  for ( i = 0; i < gnum_numeric_goal; i++ ) {
    clause = new_HCNF();
    clause->pnum = 0;
    clause->ncomp = ( Comparator * ) calloc(1, sizeof( Comparator ) );
    clause->nlhs = ( ExpNode_pointer * ) calloc(1, sizeof( ExpNode * ) );
    clause->nrhs = ( ExpNode_pointer * ) calloc(1, sizeof( ExpNode * ) );
    clause->nsign = ( Bool * ) calloc(1, sizeof( Bool ) );
    clause->nnum = 1;
    clause->ncomp[0] = gnumeric_goal_comp[i];
    clause->nlhs[0] = HCNF_get_exp(t, gnumeric_goal_lh[i]);
    clause->nrhs[0] = HCNF_get_exp(t, gnumeric_goal_rh[i]);
    clause->nsign[0] = TRUE;
    clause->prev = *cnfend;
    (*cnfend)->next = clause;
    *cnfend = clause;
    (*numclauses)++;
  }

}



/* this removes the goal clauses from the end of the HCNF.
 * must be done prior to extending the HCNF another step.
 *
 * ATTENTION: this simply removes the right number of clauses
 * from the end of the HCNF! use with care!
 *
 * clauses are stored instead of free'ed since free'ing 
 * sometimes behaves strangely and storing these 
 * few clauses doesn't matter at all anyway (avoid memory leaks, though).
 */
void HCNF_retract_goal(RPGlayer *t, 
		       HCNF **cnfend, 
		       int *numclauses)

{

  static Bool fc = TRUE;

  HCNF *clause;

  int i;



  if ( fc ) {
    gHCNFtrash = new_HCNF();
    gHCNFtrashend = gHCNFtrash;
    fc = FALSE;
  }



  for ( i = 0; i < gnum_logic_goal; i++ ) {
    clause = *cnfend;
    *cnfend = (*cnfend)->prev;
    (*cnfend)->next = NULL;
    (*numclauses)--;

    gHCNFtrashend->next = clause;
    clause->prev = gHCNFtrashend;
    gHCNFtrashend = clause;
  }

  for ( i = 0; i < gnum_numeric_goal; i++ ) {
    clause = *cnfend;
    *cnfend = (*cnfend)->prev;
    (*cnfend)->next = NULL;
    (*numclauses)--;

    gHCNFtrashend->next = clause;
    clause->prev = gHCNFtrashend;
    gHCNFtrashend = clause;
  }

}



/* outputs CNFid table and HCNF to stdout.
 * for debugging.
 */
void HCNF_print(RPGlayer *rpg,
		HCNF *cnf,
		int numvars,
		int numclauses)
     
{

  HCNF *icnf;

  RPGfact *p;
  RPGaction *a;
  RPGeffect *e;
  RPGlayer *t;
  
  int i, j;



  /* first print the "code table"
   */
  printf("\n\n-----------------------------RPG HCNF codes:");
  for ( t = rpg->next; t; t = t->next ) {
    printf("\nLayer %d:", t->t);

    for ( p = t->P->next; p; p = p->next ) {
      printf("\n%5d: fact ", p->CNFid);
      print_Fact(p->p);
    }

    for ( i = 0; i < gnum_relevant_fluents; i++ ) {
      if ( t->x_CNFid[i] == -1 ) {
	continue;
      }
      printf("\n%5d: fluent ", t->x_CNFid[i]);
      print_Fluent(&(grelevant_fluents[i]));
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
  printf("\n\n-----------------------------HCNF:");
  printf("\nnumvars: %d, numclauses: %d", numvars, numclauses);
  i = 0;
  for ( icnf = cnf->next; icnf; icnf = icnf->next ) {
    printf("\nClause %5d:", i);
    printf("\nPropositional:");
    for ( j = 0; j < icnf->pnum; j++ ) {
      if ( icnf->psign[j] ) {
	printf(" %d-", icnf->pCNFid[j]);
	HCNF_print_infostring(rpg, icnf->pCNFid[j]);
      } else {
	printf(" NOT%d-", icnf->pCNFid[j]);
	HCNF_print_infostring(rpg, icnf->pCNFid[j]);
      }
    }
    printf("\nNumeric:");
    for ( j = 0; j < icnf->nnum; j++ ) {
      printf("\n");
      if ( icnf->nsign[j] ) {
	HCNF_print_exp(rpg, icnf->nlhs[j]);
	print_comparator(icnf->ncomp[j]);
	HCNF_print_exp(rpg, icnf->nrhs[j]);
      } else {
	printf("NOT ");
	HCNF_print_exp(rpg, icnf->nlhs[j]);
	print_comparator(icnf->ncomp[j]);
	HCNF_print_exp(rpg, icnf->nrhs[j]);
      }
    }
    i++;
  }

}



void HCNF_print_exp(RPGlayer *rpg, ExpNode *exp)

{
  
  if ( !exp ) {
    return;
  }

  switch ( exp->connective ) {
  case AD:
    printf("(");
    HCNF_print_exp(rpg, exp->leftson);
    printf(" + ");
    HCNF_print_exp(rpg, exp->rightson);
    printf(")");
    break;
  case SU:
    printf("(");
    HCNF_print_exp(rpg, exp->leftson);
    printf(" - ");
    HCNF_print_exp(rpg, exp->rightson);
    printf(")");
    break;
  case MU:
    printf("(");
    HCNF_print_exp(rpg, exp->leftson);
    printf(" * ");
    HCNF_print_exp(rpg, exp->rightson);
    printf(")");
    break;
  case DI:
    printf("(");
    HCNF_print_exp(rpg, exp->leftson);
    printf(" / ");
    HCNF_print_exp(rpg, exp->rightson);
    printf(")");
    break;
  case MINUS:
    printf("(- ");
    HCNF_print_exp(rpg, exp->son);
    printf(")");
    break;
  case NUMBER:
    printf("%.2f", exp->value);
    break;
  case FHEAD:
    if ( exp->CNFid == -1 ) {
      printf("\nunset CNFid in HCNF_print_exp?\n\n");
      exit( 1 );
    }
    printf("%d-", exp->CNFid);
    HCNF_print_infostring(rpg, exp->CNFid);
    break;
  default:
    printf("\n\nHCNF_print_exp: wrong specifier %d",
	   exp->connective);
    exit( 1 );
  }

}



/* help a little in understanding what a code means, *inside*
 * the HCNF formula output.
 *
 * awkward, have to walk through entire RPG and look for that CNFid.
 */
void HCNF_print_infostring(RPGlayer *rpg, int CNFid)

{

  RPGfact *p;
  RPGaction *a;
  RPGeffect *e;
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
      if ( t->x_CNFid[i] == CNFid ) {
	printf("t%d-", t->t);
	print_Fluent(&(grelevant_fluents[i]));
	return;
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



void HCNF_statistics(RPGlayer *t, 
		     HCNF *cnf,
		     int numvars,
		     int numclauses)

{

  HCNF *icnf;
  float sum, meansize;
  int maxsize = 0;

  sum = 0;
  for ( icnf = cnf->next; icnf; icnf = icnf->next ) {
    sum += ((float) icnf->pnum);
    sum += ((float) icnf->nnum);
    if ( icnf->pnum + icnf->nnum > maxsize ) {
      maxsize = icnf->pnum + icnf->nnum;
    }
  }
  meansize = sum / ((float) numclauses);

  printf("\nHCNF layer %d: %d vars, %d clauses mean size %.2f max size %d", 
	 t->t, numvars, numclauses, meansize, maxsize);

}



/* outputs file "CNF"
 * in MATHSAT format.
 * takes in START of CNF!
 *
 * bound on plan length just for comment printout.
 */
void HCNF_output(RPGlayer *rpg,
		 HCNF *cnf,
		 int numvars,
		 int numclauses,
		 int bound)
     
{

  FILE *OUT;

  HCNF *icnf;

  RPGfact *p;
  RPGaction *a;
  RPGeffect *e;
  RPGlayer *t;

  Bool had, hadc;;
  int i;



  if ( (OUT = fopen("CNF", "w")) == NULL ) {
    printf("\ncan't open file CNF!\n\n");
    exit( 1 );
  }



  fprintf(OUT, "# HCNF from NumPDDL2HCNF, bound %d, -p %s -o %s -f %s\n\n", 
	  bound, gcmd_line.path, gcmd_line.ops_file_name, gcmd_line.fct_file_name);



  /* variable declarations.
   * 
   * put out Booleans (facts, actions, effects) and reals (fluents) 
   * in lines corresponding to RPG layers.
   */
  fprintf(OUT, "VAR\n");
  for ( t = rpg->next; t; t = t->next ) {
    
    had = FALSE;
    for ( p = t->P->next; p; p = p->next ) {
      if ( had ) {
	fprintf(OUT, ", ");
      }
      had = TRUE;
      fprintf(OUT, "B%d", p->CNFid);
    }
    if ( had ) {
      fprintf(OUT, ": BOOLEAN\n");
    }

    had = FALSE;
    for ( i = 0; i < gnum_relevant_fluents; i++ ) {
      if ( t->x_CNFid[i] == -1 ) {
	continue;
      }
      if ( had ) {
	fprintf(OUT, ", ");
      }
      had = TRUE;
      fprintf(OUT, "R%d", t->x_CNFid[i]);
    }
    if ( had ) {
      fprintf(OUT, ": REAL\n");
    }

    if ( t->A ) {
      had = FALSE;
      for ( a = t->A->next; a; a = a->next ) {
	if ( had ) {
	  fprintf(OUT, ", ");
	}
	had = TRUE;
	fprintf(OUT, "B%d", a->CNFid);
	for ( e = a->E->next; e; e = e->next ) {
	  fprintf(OUT, ", B%d", e->CNFid);
	}
      }
      if ( had ) {
	fprintf(OUT, ": BOOLEAN\n"); 
      }     
    }
  } /* endfor t over RPG layers */
  fprintf(OUT, "\n");
  


  /* The formula.
   */
  fprintf(OUT, "FORMULA\n");
  hadc = FALSE;
  for ( icnf = cnf->next; icnf; icnf = icnf->next ) {
    if ( hadc ) {
      fprintf(OUT, "& ");
    }
    fprintf(OUT, "(");
    hadc = TRUE;

    had = FALSE;

    /* propositional part.
     */
    for ( i = 0; i < icnf->pnum; i++ ) {
      if ( had ) {
	fprintf(OUT, " | ");
      }
      had = TRUE;

      if ( !icnf->psign[i] ) {
	fprintf(OUT, "(!");
      }

      fprintf(OUT, "B%d", icnf->pCNFid[i]);

      if ( !icnf->psign[i] ) {
	fprintf(OUT, ")");
      }
    } /* endfor i over propositional part of icnf */

    /* numeric part.
     */
    for ( i = 0; i < icnf->nnum; i++ ) {
      if ( had ) {
	fprintf(OUT, " | ");
      }
      had = TRUE;

      if ( !icnf->nsign[i] ) {
	fprintf(OUT, "(!");
      }

      fprintf(OUT, "(");
      HCNF_output_exp(OUT, icnf->nlhs[i]);
      switch ( icnf->ncomp[i] ) {
      case LE:
	fprintf(OUT, " < ");
	break;
      case LEQ:
	fprintf(OUT, " <= ");
	break;
      case EQ:
	fprintf(OUT, " = ");
	break;
      case GEQ:
	fprintf(OUT, " >= ");
	break;
      case GE:
	fprintf(OUT, " > ");
	break;
      default:
	printf("\n\nillegal comparator in print HCNF_output");
	exit( 1 );
      }
      HCNF_output_exp(OUT, icnf->nrhs[i]);
      fprintf(OUT, ")");

      if ( !icnf->nsign[i] ) {
	fprintf(OUT, ")");
      }
    } /* endfor i over numeric part of icnf */

    fprintf(OUT, ")\n");/* matches clause start "(" */
  } /* endfor icnf over HCNF clauses */
  fprintf(OUT, "\n\n");

  fclose(OUT);

}



void HCNF_output_exp(FILE *OUT, ExpNode *exp)

{
  
  if ( !exp ) {
    return;
  }

  switch ( exp->connective ) {
  case AD:
    fprintf(OUT, "(");
    HCNF_output_exp(OUT, exp->leftson);
    fprintf(OUT, " + ");
    HCNF_output_exp(OUT, exp->rightson);
    fprintf(OUT, ")");
    break;
  case SU:
    fprintf(OUT, "(");
    HCNF_output_exp(OUT, exp->leftson);
    fprintf(OUT, " - ");
    HCNF_output_exp(OUT, exp->rightson);
    fprintf(OUT, ")");
    break;
  case MU:
    fprintf(OUT, "(");
    HCNF_output_exp(OUT, exp->leftson);
    fprintf(OUT, " * ");
    HCNF_output_exp(OUT, exp->rightson);
    fprintf(OUT, ")");
    break;
  case DI:
    fprintf(OUT, "(");
    HCNF_output_exp(OUT, exp->leftson);
    fprintf(OUT, " / ");
    HCNF_output_exp(OUT, exp->rightson);
    fprintf(OUT, ")");
    break;
  case MINUS:
    fprintf(OUT, "(- ");
    HCNF_output_exp(OUT, exp->son);
    fprintf(OUT, ")");
    break;
  case NUMBER:
    fprintf(OUT, "%f", exp->value);
    break;
  case FHEAD:
    if ( exp->CNFid == -1 ) {
      printf("\nunset CNFid in HCNF_output_exp?\n\n");
      exit( 1 );
    }
    fprintf(OUT, "R%d", exp->CNFid);
    break;
  default:
    printf("\n\nHCNF_output_exp: wrong specifier %d",
	   exp->connective);
    exit( 1 );
  }

}



































/* -------------------------------------------------------------------------------
 * getting specific clauses.
 */































  

void HCNF_get_pre_con(RPGlayer *t, 
		      HCNF **cnfend, 
		      int *numclauses)

{

  HCNF *clause;
  
  RPGaction *a;
  RPGeffect *e;
  RPGfact *p;

  int i;



  for ( a = t->A->next; a; a = a->next ) {
    /* pre clauses for a: facts -- (-a or p)
     */
    for ( i = 0; i < a->a->num_preconds; i++ ) {
      clause = new_HCNF();
      clause->pCNFid = ( int * ) calloc(2, sizeof( int ) );
      clause->psign = ( Bool * ) calloc(2, sizeof( Bool ) );
      clause->pnum = 2;
      clause->pCNFid[0] = a->CNFid;
      clause->psign[0] = FALSE;
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
      clause->pCNFid[1] = p->CNFid;
      clause->psign[1] = TRUE;      
      clause->nnum = 0;
      clause->prev = *cnfend;
      (*cnfend)->next = clause;
      *cnfend = clause;
      (*numclauses)++;
    } /* endfor i over prop prec */



    /* pre clauses for a: num constr -- (-a or (exp comp exp'))
     */
    for ( i = 0; i < a->a->num_numeric_preconds; i++ ) {
      clause = new_HCNF();
      clause->pCNFid = ( int * ) calloc(1, sizeof( int ) );
      clause->psign = ( Bool * ) calloc(1, sizeof( Bool ) );
      clause->pnum = 1;
      clause->pCNFid[0] = a->CNFid;
      clause->psign[0] = FALSE;

      clause->ncomp = ( Comparator * ) calloc(1, sizeof( Comparator ) );
      clause->nlhs = ( ExpNode_pointer * ) calloc(1, sizeof( ExpNode * ) );
      clause->nrhs = ( ExpNode_pointer * ) calloc(1, sizeof( ExpNode * ) );
      clause->nsign = ( Bool * ) calloc(1, sizeof( Bool ) );
      clause->nnum = 1;
      clause->ncomp[0] = a->a->numeric_preconds_comp[i];
      clause->nlhs[0] = HCNF_get_exp(t, a->a->numeric_preconds_lh[i]);
      clause->nrhs[0] = HCNF_get_exp(t, a->a->numeric_preconds_rh[i]);
      clause->nsign[0] = TRUE;

      clause->prev = *cnfend;
      (*cnfend)->next = clause;
      *cnfend = clause;
      (*numclauses)++;
    } /* endfor i over numeric prec */


    
    /* con clauses for all e
     */
    for ( e = a->E->next; e; e = e->next ) {
      /* facts -- (-e or p)
       */
      for ( i = 0; i < e->e->num_conditions; i++ ) {
	clause = new_HCNF();
	clause->pCNFid = ( int * ) calloc(2, sizeof( int ) );
	clause->psign = ( Bool * ) calloc(2, sizeof( Bool ) );
	clause->pnum = 2;
	clause->pCNFid[0] = e->CNFid;
	clause->psign[0] = FALSE;
	for ( p = t->P->next; p; p = p->next ) {
	  if ( p->id == e->e->conditions[i] ) {
	    break;
	  }
	}
	if ( !p ) {
	  printf("\ncan't find condition in con clause?\n\n");
	  exit( 1 );
	}
	clause->pCNFid[1] = p->CNFid;
	clause->psign[1] = TRUE;      
	clause->nnum = 0;
	clause->prev = *cnfend;
	(*cnfend)->next = clause;
	*cnfend = clause;
	(*numclauses)++;
      } /* endfor i over prop cond */



      /* num constr -- (-e or (exp comp exp'))
       */
      for ( i = 0; i < e->e->num_numeric_conditions; i++ ) {
	clause = new_HCNF();
	clause->pCNFid = ( int * ) calloc(1, sizeof( int ) );
	clause->psign = ( Bool * ) calloc(1, sizeof( Bool ) );
	clause->pnum = 1;
	clause->pCNFid[0] = e->CNFid;
	clause->psign[0] = FALSE;

	clause->ncomp = ( Comparator * ) calloc(1, sizeof( Comparator ) );
	clause->nlhs = ( ExpNode_pointer * ) calloc(1, sizeof( ExpNode * ) );
	clause->nrhs = ( ExpNode_pointer * ) calloc(1, sizeof( ExpNode * ) );
	clause->nsign = ( Bool * ) calloc(1, sizeof( Bool ) );
	clause->nnum = 1;
	clause->ncomp[0] = e->e->numeric_conditions_comp[i];
	clause->nlhs[0] = HCNF_get_exp(t, e->e->numeric_conditions_lh[i]);
	clause->nrhs[0] = HCNF_get_exp(t, e->e->numeric_conditions_rh[i]);
	clause->nsign[0] = TRUE;

	clause->prev = *cnfend;
	(*cnfend)->next = clause;
	*cnfend = clause;
	(*numclauses)++;
      } /* endfor i over numeric cond */
    } /* endfor e over a->E */
  } /* endfor a over t->A */

}



void HCNF_get_ea_ae(RPGlayer *t, 
		    HCNF **cnfend, 
		    int *numclauses)

{

  HCNF *clause;
  
  RPGaction *a;
  RPGeffect *e;
  RPGfact *p;

  int i, num;



  /* for all e: (-e or a(e))
   */
  for ( a = t->A->next; a; a = a->next ) {
    for ( e = a->E->next; e; e = e->next ) {
      clause = new_HCNF();
      clause->pCNFid = ( int * ) calloc(2, sizeof( int ) );
      clause->psign = ( Bool * ) calloc(2, sizeof( Bool ) );
      clause->pnum = 2;
      clause->pCNFid[0] = e->CNFid;
      clause->psign[0] = FALSE;
      clause->pCNFid[1] = a->CNFid;
      clause->psign[1] = TRUE;      
      clause->nnum = 0;
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
      clause = new_HCNF();

      num = 2 + e->e->num_conditions;/* a, e, prop con */
      clause->pCNFid = ( int * ) calloc(num, sizeof( int ) );
      clause->psign = ( Bool * ) calloc(num, sizeof( Bool ) );
      clause->pnum = num;
      clause->pCNFid[0] = a->CNFid;
      clause->psign[0] = FALSE;
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
	clause->pCNFid[num] = p->CNFid;
	clause->psign[num] = FALSE;
	num++;
      }
      clause->pCNFid[num] = e->CNFid;
      clause->psign[num] = TRUE;

      clause->ncomp = ( Comparator * ) 
	calloc(e->e->num_numeric_conditions, sizeof( Comparator ) );
      clause->nlhs = ( ExpNode_pointer * ) 
	calloc(e->e->num_numeric_conditions, sizeof( ExpNode * ) );
      clause->nrhs = ( ExpNode_pointer * ) 
	calloc(e->e->num_numeric_conditions, sizeof( ExpNode * ) );
      clause->nsign = ( Bool * ) calloc(e->e->num_numeric_conditions, sizeof( Bool ) );
      clause->nnum = e->e->num_numeric_conditions;
      for ( i = 0; i < e->e->num_numeric_conditions; i++ ) {
	clause->ncomp[i] = e->e->numeric_conditions_comp[i];
	clause->nlhs[i] = HCNF_get_exp(t, e->e->numeric_conditions_lh[i]);
	clause->nrhs[i] = HCNF_get_exp(t, e->e->numeric_conditions_rh[i]);
	clause->nsign[i] = FALSE;
      }

      clause->prev = *cnfend;
      (*cnfend)->next = clause;
      *cnfend = clause;
      (*numclauses)++;
    } /* endfor e over effects */
  } /* endfor a over actions */

}



void HCNF_get_eff(RPGlayer *t, 
		  HCNF **cnfend, 
		  int *numclauses)

{

  /* this stuff is like in RPG_insert_effect, RPG.c
   */
  static ExpNode *exp, *lhsnode;
  static Bool fc = TRUE;

  HCNF *clause;
  
  RPGaction *a;
  RPGeffect *e;
  RPGfact *p;
  RPGlayer *tpp = t->next;

  int i;



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
	clause = new_HCNF();
	clause->pCNFid = ( int * ) calloc(2, sizeof( int ) );
	clause->psign = ( Bool * ) calloc(2, sizeof( Bool ) );
	clause->pnum = 2;
	clause->pCNFid[0] = e->CNFid;
	clause->psign[0] = FALSE;
	clause->pCNFid[1] = p->CNFid;
	clause->psign[1] = TRUE;      
	clause->nnum = 0;
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
	clause = new_HCNF();
	clause->pCNFid = ( int * ) calloc(2, sizeof( int ) );
	clause->psign = ( Bool * ) calloc(2, sizeof( Bool ) );
	clause->pnum = 2;
	clause->pCNFid[0] = e->CNFid;
	clause->psign[0] = FALSE;
	clause->pCNFid[1] = p->CNFid;
	clause->psign[1] = FALSE;      
	clause->nnum = 0;
	clause->prev = *cnfend;
	(*cnfend)->next = clause;
	*cnfend = clause;
	(*numclauses)++;
      }



      /* for all e, (x := exp) in e: (-e_t or x_t+1 = exp_t)
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

	clause = new_HCNF();
	clause->pCNFid = ( int * ) calloc(1, sizeof( int ) );
	clause->psign = ( Bool * ) calloc(1, sizeof( Bool ) );
	clause->pnum = 1;
	clause->pCNFid[0] = e->CNFid;
	clause->psign[0] = FALSE;

	clause->ncomp = ( Comparator * ) calloc(1, sizeof( Comparator ) );
	clause->nlhs = ( ExpNode_pointer * ) calloc(1, sizeof( ExpNode * ) );
	clause->nrhs = ( ExpNode_pointer * ) calloc(1, sizeof( ExpNode * ) );
	clause->nsign = ( Bool * ) calloc(1, sizeof( Bool ) );
	clause->nnum = 1;
	clause->ncomp[0] = EQ;
	if ( !tpp->x_CNFid || tpp->x_CNFid[e->e->numeric_effects_fl[i]] == -1 ) {
	  printf("\nx tpp %d CNFid %d in HCNF get eff not set?\n\n",
		 tpp->t, e->e->numeric_effects_fl[i]);
	  exit( 1 );
	}
	clause->nlhs[0] = new_ExpNode(FHEAD);
	clause->nlhs[0]->CNFid = tpp->x_CNFid[e->e->numeric_effects_fl[i]];
	if ( e->e->numeric_effects_neft[i] != ASSIGN ) {
	  clause->nrhs[0] = HCNF_get_exp(t, exp);
	} else {
	  clause->nrhs[0] = HCNF_get_exp(t, e->e->numeric_effects_rh[i]);
	}
	clause->nsign[0] = TRUE;

	clause->prev = *cnfend;
	(*cnfend)->next = clause;
	*cnfend = clause;
	(*numclauses)++;
      } /* endfor i over numeric effects */
    } /* endfor e over effects */
  } /* endfor a over actions */

}



void HCNF_get_frame(RPGlayer *t, 
		    HCNF **cnfend, 
		    int *numclauses)

{

  HCNF *clause;
  
  RPGfact *p, *ptpp;
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
    clause = new_HCNF();
    clause->pCNFid = ( int * ) calloc(num+2, sizeof( int ) );
    clause->psign = ( Bool * ) calloc(num+2, sizeof( Bool ) );
    clause->pnum = num+2;
    clause->pCNFid[0] = p->CNFid;
    clause->psign[0] = FALSE;
    num = 1;
    for ( el = t->tD[p->id]->next; el; el = el->next ) {
      clause->pCNFid[num] = el->e->CNFid;
      clause->psign[num] = TRUE;
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
    clause->pCNFid[num] = ptpp->CNFid;
    clause->psign[num] = TRUE;
    clause->nnum = 0;
    (*cnfend)->next = clause;
    *cnfend = clause;
    (*numclauses)++;

    /* now the negative frame clause
     */
    num = 0;
    for ( el = t->tA[p->id]->next; el; el = el->next ) {
      num++;
    }
    clause = new_HCNF();
    clause->pCNFid = ( int * ) calloc(num+2, sizeof( int ) );
    clause->psign = ( Bool * ) calloc(num+2, sizeof( Bool ) );
    clause->pnum = num+2;
    clause->pCNFid[0] = p->CNFid;
    clause->psign[0] = TRUE;
    num = 1;
    for ( el = t->tA[p->id]->next; el; el = el->next ) {
      clause->pCNFid[num] = el->e->CNFid;
      clause->psign[num] = TRUE;
      num++;
    }
    /* we still got p_tpp from above.
     */
    clause->pCNFid[num] = ptpp->CNFid;
    clause->psign[num] = FALSE;
    clause->nnum = 0;
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
    clause = new_HCNF();
    clause->pCNFid = ( int * ) calloc(num+1, sizeof( int ) );
    clause->psign = ( Bool * ) calloc(num+1, sizeof( Bool ) );
    clause->pnum = num+1;
    num = 0;
    for ( el = t->tA[ptpp->id]->next; el; el = el->next ) {
      clause->pCNFid[num] = el->e->CNFid;
      clause->psign[num] = TRUE;
      num++;
    }
    clause->pCNFid[num] = ptpp->CNFid;
    clause->psign[num] = FALSE;
    clause->nnum = 0;
    (*cnfend)->next = clause;
    *cnfend = clause;
    (*numclauses)++;
  }



  /* fluent frame clauses:
   * for all fluents x that have at least one value at t:
   *     (OR{e_t | (x:=exp) in e} or x_tpp=x_t)
   */
  for ( i = 0; i < gnum_relevant_fluents; i++ ) {
    if ( !t->V[i]->next ) {
      continue;
    }

    clause = new_HCNF();

    num = 0;
    for ( el = t->tXA[i]->next; el; el = el->next ) {
      num++;
    }
    clause->pCNFid = ( int * ) calloc(num, sizeof( int ) );
    clause->psign = ( Bool * ) calloc(num, sizeof( Bool ) );
    clause->pnum = num;
    num = 0;
    for ( el = t->tXA[i]->next; el; el = el->next ) {
      clause->pCNFid[num] = el->e->CNFid;
      clause->psign[num] = TRUE;
      num++;
    }

    clause->ncomp = ( Comparator * ) calloc(1, sizeof( Comparator ) );
    clause->nlhs = ( ExpNode_pointer * ) calloc(1, sizeof( ExpNode * ) );
    clause->nrhs = ( ExpNode_pointer * ) calloc(1, sizeof( ExpNode * ) );
    clause->nsign = ( Bool * ) calloc(1, sizeof( Bool ) );
    clause->nnum = 1;
    clause->ncomp[0] = EQ;
    if ( !tpp->x_CNFid || tpp->x_CNFid[i] == -1 ) {
      printf("\nx tpp CNFid in HCNF get frame not set?\n\n");
      exit( 1 );
    }
    clause->nlhs[0] = new_ExpNode(FHEAD);
    clause->nlhs[0]->CNFid = tpp->x_CNFid[i];
    if ( !t->x_CNFid || t->x_CNFid[i] == -1 ) {
      printf("\nx t CNFid in HCNF get frame not set?\n\n");
      exit( 1 );
    }
    clause->nrhs[0] = new_ExpNode(FHEAD);
    clause->nrhs[0]->CNFid = t->x_CNFid[i];
    clause->nsign[0] = TRUE;

    clause->prev = *cnfend;
    (*cnfend)->next = clause;
    *cnfend = clause;
    (*numclauses)++;
  } /* endfor i over fluent indices */

}



/* (-a or -e) for all a not| e
 * either e dels a pre of a, or e affects an x mentioned in a's numpre.
 */
void HCNF_get_aemutex(RPGlayer *t, 
		      HCNF **cnfend, 
		      int *numclauses)

{

  /* to avoid duplicates
   */
  static Bool fc = TRUE;
  static Bool **had;

  HCNF *clause;
  
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
	had[al->a->a->id][el->e->e->id] = TRUE;
	clause = new_HCNF();
	clause->pCNFid = ( int * ) calloc(2, sizeof( int ) );
	clause->psign = ( Bool * ) calloc(2, sizeof( Bool ) );
	clause->pnum = 2;
	clause->pCNFid[0] = al->a->CNFid;
	clause->psign[0] = FALSE;
	clause->pCNFid[1] = el->e->CNFid;
	clause->psign[1] = FALSE;      
	clause->nnum = 0;
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
	had[al->a->a->id][el->e->e->id] = TRUE;
	clause = new_HCNF();
	clause->pCNFid = ( int * ) calloc(2, sizeof( int ) );
	clause->psign = ( Bool * ) calloc(2, sizeof( Bool ) );
	clause->pnum = 2;
	clause->pCNFid[0] = al->a->CNFid;
	clause->psign[0] = FALSE;
	clause->pCNFid[1] = el->e->CNFid;
	clause->psign[1] = FALSE;      
	clause->nnum = 0;
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
void HCNF_get_eemutex(RPGlayer *t, 
		      HCNF **cnfend, 
		      int *numclauses)

{

  /* to avoid duplicates
   */
  static Bool fc = TRUE;
  static Bool **had;

  HCNF *clause;
  
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
	had[el1->e->e->id][el2->e->e->id] = TRUE;
	clause = new_HCNF();
	clause->pCNFid = ( int * ) calloc(2, sizeof( int ) );
	clause->psign = ( Bool * ) calloc(2, sizeof( Bool ) );
	clause->pnum = 2;
	clause->pCNFid[0] = el1->e->CNFid;
	clause->psign[0] = FALSE;
	clause->pCNFid[1] = el2->e->CNFid;
	clause->psign[1] = FALSE;      
	clause->nnum = 0;
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
	had[el1->e->e->id][el2->e->e->id] = TRUE;
	clause = new_HCNF();
	clause->pCNFid = ( int * ) calloc(2, sizeof( int ) );
	clause->psign = ( Bool * ) calloc(2, sizeof( Bool ) );
	clause->pnum = 2;
	clause->pCNFid[0] = el1->e->CNFid;
	clause->psign[0] = FALSE;
	clause->pCNFid[1] = el2->e->CNFid;
	clause->psign[1] = FALSE;      
	clause->nnum = 0;
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
	had[el1->e->e->id][el2->e->e->id] = TRUE;
	clause = new_HCNF();
	clause->pCNFid = ( int * ) calloc(2, sizeof( int ) );
	clause->psign = ( Bool * ) calloc(2, sizeof( Bool ) );
	clause->pnum = 2;
	clause->pCNFid[0] = el1->e->CNFid;
	clause->psign[0] = FALSE;
	clause->pCNFid[1] = el2->e->CNFid;
	clause->psign[1] = FALSE;      
	clause->nnum = 0;
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
	had[el1->e->e->id][el2->e->e->id] = TRUE;
	clause = new_HCNF();
	clause->pCNFid = ( int * ) calloc(2, sizeof( int ) );
	clause->psign = ( Bool * ) calloc(2, sizeof( Bool ) );
	clause->pnum = 2;
	clause->pCNFid[0] = el1->e->CNFid;
	clause->psign[0] = FALSE;
	clause->pCNFid[1] = el2->e->CNFid;
	clause->psign[1] = FALSE;      
	clause->nnum = 0;
	clause->prev = *cnfend;
	(*cnfend)->next = clause;
	*cnfend = clause;
	(*numclauses)++;
      }
    }
  } /* endfor i over fluent indices */

}



/* just say that every fluent has to have one
 * of its values listed in the RPG at this time.
 */
void HCNF_get_tvalue(RPGlayer *t, 
		     HCNF **cnfend, 
		     int *numclauses)

{

  HCNF *clause;

  RPGvalue *v;

  int i, num;



  for ( i = 0; i < gnum_relevant_fluents; i++ ) {
    if ( !t->V[i]->next ) {
      continue;
    }
    clause = new_HCNF();
    num = 0;
    for ( v = t->V[i]->next; v; v = v->next ) {
      num++;
    }
    clause->pnum = 0;
    clause->ncomp = ( Comparator * ) calloc(num, sizeof( Comparator ) );
    clause->nlhs = ( ExpNode_pointer * ) calloc(num, sizeof( ExpNode * ) );
    clause->nrhs = ( ExpNode_pointer * ) calloc(num, sizeof( ExpNode * ) );
    clause->nsign = ( Bool * ) calloc(num, sizeof( Bool ) );
    clause->nnum = num;
    num = 0;
    for ( v = t->V[i]->next; v; v = v->next ) {
      clause->ncomp[num] = EQ;
      if ( !t->x_CNFid || t->x_CNFid[i] == -1 ) {
	printf("\nx t CNFid in HCNF get tvalue not set?\n\n");
	exit( 1 );
      }
      clause->nlhs[num] = new_ExpNode(FHEAD);
      clause->nlhs[num]->CNFid = t->x_CNFid[i];
      clause->nrhs[num] = new_ExpNode(NUMBER);
      clause->nrhs[num]->value = v->v;
      clause->nsign[num] = TRUE;
      num++;
    }
    clause->prev = *cnfend;
    (*cnfend)->next = clause;
    *cnfend = clause;
    (*numclauses)++;
  }

}

























/* -------------------------------------------------------------------------------
 * some helpers.
 */

























/* create a copy in which the fluent CNFid is set as specified
 * in t.
 */
ExpNode *HCNF_get_exp(RPGlayer *t, ExpNode *exp)

{

  ExpNode *res;

  if ( !exp ) {
    return NULL;
  }
  
  res = new_ExpNode( exp->connective );

  switch ( exp->connective ) {
  case FHEAD:
    if ( !t->x_CNFid || t->x_CNFid[exp->fl] == -1 ) {
      printf("\nfluent id not set in HCNF get exp?\n\n");
      exit( 1 );
    }
    res->CNFid = t->x_CNFid[exp->fl];
    break;
  case NUMBER:
    res->value = exp->value;
    break;
  case MINUS:
    res->son = HCNF_get_exp(t, exp->son);
    break;
  case AD:
  case SU:
  case MU:
  case DI:
    res->leftson = HCNF_get_exp(t, exp->leftson);
    res->rightson = HCNF_get_exp(t, exp->rightson);
    break;
  default:
    printf("\nunknown exo connective in HCNF get exp?\n\n");
    exit( 1 );
  }

  return res;

}

