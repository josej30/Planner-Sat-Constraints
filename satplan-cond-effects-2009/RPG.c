

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
 * File: RPG.c
 * Description: functions building fully-fledged numeric RPG
 *              from pre-"conn" data structures.
 *
 * NOT runtime optimized!! Assumed to be built only once.
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




















/* -------------------------------------------------------------------------------
 * main overlooking functions.
 */





















/* take dummy start layer and return first
 * RPG layer.
 */
RPGlayer *RPG_initialize( RPGlayer *RPG )

{

  RPGlayer *t;
  RPGfact *p, *prevp;
  RPGvalue *v;

  int i;

  if ( gcmd_line.debug && gcmd_line.dRPG ) {
    printf("\n\n\ninitializing RPG.");
  }



  /* layer nr. 0 facts and fluents
   */
  t = new_RPGlayer();
  t->t = 0;
  t->prev = RPG;
  RPG->next = t;

  /* facts
   */
  t->P = new_RPGfact();
  t->is_P = ( Bool * ) calloc(gnum_relevant_facts, sizeof( Bool ));
  for ( i = 0; i < gnum_relevant_facts; i++ ) {
    t->is_P[i] = FALSE;
  }
  prevp = t->P;
  for ( i = 0; i < ginitial_state.num_F; i++ ) {
    p = new_RPGfact();
    p->p = &(grelevant_facts[ginitial_state.F[i]]);
    p->id = ginitial_state.F[i];
    t->is_P[p->id] = TRUE;
    p->prev = prevp;
    prevp->next = p;
    prevp = p;
  }
  t->endP = prevp;

  /* fluent values
   */
  t->V = ( RPGvalue_pointer * ) calloc(gnum_relevant_fluents, sizeof(RPGvalue_pointer));
  for ( i = 0; i < gnum_relevant_fluents; i++ ) {
    t->V[i] = new_RPGvalue();

    if ( !ginitial_state.f_D[i] ) {
      /* simply leave this empty! will be automatically
       * handled in the right way .. ?!
       */
      continue;
/*       printf("\ninitially undefined fluent! sorry but I'm not doing these right now.\n\n"); */
/*       exit( 1 ); */
    }

    v = new_RPGvalue();
    v->v = ginitial_state.f_V[i];
    v->prev = t->V[i];
    t->V[i]->next = v;
  }

  /* constraint value tuples
   */
  t->constraint_VT = ( RPGvaluetuple_pointer * ) 
    calloc(gnum_relevant_constraints, sizeof(RPGvaluetuple_pointer));
  for ( i = 0; i < gnum_relevant_constraints; i++ ) {
    t->constraint_VT[i] = new_RPGvaluetuple();

    RPG_get_constraint_valuetuples(t, i);
  }

  /* psi value tuples
   */
  t->psi_VT = ( RPGvaluetuple_pointer * ) 
    calloc(gnum_relevant_psis, sizeof(RPGvaluetuple_pointer));
  for ( i = 0; i < gnum_relevant_psis; i++ ) {
    t->psi_VT[i] = new_RPGvaluetuple();

    RPG_get_psi_valuetuples(t, i);
  }

  return t;

}



/* take RPG layer t, insert actions into t,
 * create next layer tpp and insert facts and fluent stuff,
 * return tpp.
 */
RPGlayer *RPG_extend( RPGlayer *t )

{

  RPGlayer *tpp;
  RPGfact *p, *prevp, *ip;
  RPGvalue *v, *prevv, *iv;
  RPGaction *a;
  RPGeffect *e, *ie;

  int i, j, k;
  Action *ga;
  ActionEffect *ge;



  if ( gcmd_line.debug && gcmd_line.dRPG ) {
    printf("\n\n\n\nextending RPG.");
  }



  tpp = new_RPGlayer();
  tpp->t = t->t+1;
  tpp->prev = t;
  t->next = tpp;



  /* initialize facts to facts at t.
   */
  tpp->P = new_RPGfact();
  tpp->is_P = ( Bool * ) calloc(gnum_relevant_facts, sizeof( Bool ));
  for ( i = 0; i < gnum_relevant_facts; i++ ) {
    tpp->is_P[i] = FALSE;
  }
  prevp = tpp->P;
  for ( ip = t->P->next; ip; ip = ip->next ) {
    p = new_RPGfact();
    p->p = ip->p;
    p->id = ip->id;
    tpp->is_P[p->id] = TRUE;
    p->prev = prevp;
    prevp->next = p;
    prevp = p;
  }
  tpp->endP = prevp;

  /* initialize fluent values to fluent values at t.
   */
  tpp->V = ( RPGvalue_pointer * ) calloc(gnum_relevant_fluents, sizeof(RPGvalue_pointer));
  for ( i = 0; i < gnum_relevant_fluents; i++ ) {
    tpp->V[i] = new_RPGvalue();

    prevv = tpp->V[i];
    for ( iv = t->V[i]->next; iv; iv = iv->next ) {
      v = new_RPGvalue();
      v->v = iv->v;
      v->prev = prevv;
      prevv->next = v;
      prevv = v;
    }
  }

  /* the value tuples will be collected completely anew from tpp,
   * once the values at tpp have been completed.
   *
   * NOTE: this may be made significantly more efficient by
   * distinguishing between old and new var values, copying over the 
   * old tuples here, and collect new tuples below only for the new var 
   * values. skip for now since I don't expect all that many RPG layers 
   * anyway.
   *
   * NOTE however: actually i just tried the above (see OLD/)
   * it's quite complicated since actually we have to build tuples
   * not entirely out of new values, but so that they contain *at least*
   * one new value. implementing this in the context here, with arbitrary
   * expressions, doesn't strike me as very desirable...
   * does not have much of an effect anyway, in most domains. leave it for now.
   */

  /* constraint value tuples
   */
  tpp->constraint_VT = ( RPGvaluetuple_pointer * ) 
    calloc(gnum_relevant_constraints, sizeof(RPGvaluetuple_pointer));
  for ( i = 0; i < gnum_relevant_constraints; i++ ) {
    tpp->constraint_VT[i] = new_RPGvaluetuple();
  }
  /* psi value tuples
   */
  tpp->psi_VT = ( RPGvaluetuple_pointer * ) 
    calloc(gnum_relevant_psis, sizeof(RPGvaluetuple_pointer));
  for ( i = 0; i < gnum_relevant_psis; i++ ) {
    tpp->psi_VT[i] = new_RPGvaluetuple();
  }

  /* actions at t. don't copy anything over since we will have to
   * re-consider each action anyway, to check for new numeric
   * effects.
   */
  t->A = new_RPGaction();
  t->endA = t->A;
  if ( gcmd_line.debug > 2 && gcmd_line.dRPG ) {
    printf("\n\n\nfinished RPG copy. now is:");
    RPG_print();
  }


  /* find the applicable actions/effects, and insert the new facts/values.
   */
  i = 0;
  for ( ga = gactions; ga; ga = ga->next ) {
    if ( gcmd_line.debug && gcmd_line.dRPG ) {
      printf("\ntrying action: "); print_Action_name(ga);
    }

    /* check applicability!
     */
    if ( gcmd_line.debug && gcmd_line.dRPG ) {
      printf("\napplicable checking");
    }
    if ( !RPG_a_applicable(t, ga) ) {
      if ( gcmd_line.debug && gcmd_line.dRPG ) {
	printf("\napplicable NO!");
      }
      i++;
      continue;
    }
    if ( gcmd_line.debug && gcmd_line.dRPG ) {
      printf("\napplicable YES!");
    }
    /* insert action!
     */
    a = new_RPGaction();
    a->a = ga;
    a->id = i;
    a->prev = t->endA;
    t->endA->next = a;
    t->endA = a;
    a->E = new_RPGeffect();

    /* check the effects.
     */
    for ( j = 0; j < ga->num_effects; j++ ) {
      ge = &(ga->effects[j]);
      if ( gcmd_line.debug && gcmd_line.dRPG ) {
	printf("\ntrying effect: %d", j);
      }

      /* check applicability!
       */
      if ( gcmd_line.debug && gcmd_line.dRPG ) {
	printf("\napplicable checking effect");
      }
      if ( !RPG_e_applicable(t, ge) ) {
	if ( gcmd_line.debug && gcmd_line.dRPG ) {
	  printf("\napplicable NO!");
	}
	continue;
      }
      if ( gcmd_line.debug && gcmd_line.dRPG ) {
	printf("\napplicable YES!");
      }
      /* insert effect!
       */
      e = new_RPGeffect();
      e->e = ge;
      e->id = j;
      /* find last list element. 
       * INEFFICIENT!
       *
       * probably not so bad since we don't expect single actions to
       * have huge numbers of effects.
       */
      for ( ie = a->E; ie->next; ie = ie->next );
      e->prev = ie;
      ie->next = e;
   
      /* insert new added facts!
       */
      for ( k = 0; k < ge->num_adds; k++ ) {
	if ( gcmd_line.debug && gcmd_line.dRPG ) {
	  printf("\ntrying add effect: ");
	  print_ft_name(ge->adds[k]);
	}

	/* check if this is new!
	 */
	if ( RPG_P_contains(tpp, ge->adds[k]) ) {
	  if ( gcmd_line.debug && gcmd_line.dRPG ) {
	    printf(" not new!");
	  }
	  continue;
	}
	if ( gcmd_line.debug && gcmd_line.dRPG ) {
	  printf(" new!");
	}
	
	/* insert this into the facts.
	 */
	p = new_RPGfact();
	p->p = &(grelevant_facts[ge->adds[k]]);
	p->id = ge->adds[k];
	tpp->is_P[p->id] = TRUE;
	p->prev = tpp->endP;
	tpp->endP->next = p;
	tpp->endP = p;
      } /* endfor k over adds of ge */

      /* insert new fluent values!
       */
      for ( k = 0; k < ge->num_numeric_effects; k++ ) {
	RPG_insert_effect(t,
			  ge->con_psi_id,
			  ge->numeric_effects_fl[k],
			  ge->numeric_effects_neft[k],
			  ge->numeric_effects_rh[k]);
      } /* endfor k over numeric effects of ge */
    } /* endfor j over effects ge of ga */

    i++;
  } /* endfor ga over actions, index i kept up-to-date */
  if ( gcmd_line.debug > 2 && gcmd_line.dRPG ) {
    printf("\n\n\nfinished actions. now is:");
    RPG_print();
  }



  /* now all values at tpp are inserted. we need to compute
   * the extensions of the constraints and psis!
   */
  for ( i = 0; i < gnum_relevant_constraints; i++ ) {
    RPG_get_constraint_valuetuples(tpp, i);
  }
  for ( i = 0; i < gnum_relevant_psis; i++ ) {
    RPG_get_psi_valuetuples(tpp, i);
  }
  if ( gcmd_line.debug > 2 && gcmd_line.dRPG ) {
    printf("\n\n\nfinished constraints and psis. now is:");
    RPG_print();
  }



  /* set up the connectivity info that will be needed
   * for generation of frame and mutex clauses.
   *
   * associated to the *action* layer!
   */
  RPG_get_connectivity(t);



  return tpp;

}



Bool RPG_satisfiesgoal( RPGlayer *t )

{

  int i;

  /* first, propositions.
   */
  for ( i = 0; i < gnum_logic_goal; i++ ) {
    if ( !RPG_P_contains(t, glogic_goal[i]) ) {
      if ( gcmd_line.debug && gcmd_line.dRPG ) {
	printf("\nprop goal no!");
      }
      return FALSE;
    }
  }
  if ( gcmd_line.debug && gcmd_line.dRPG ) {
    printf("\nprop goal yes!");
  }
  
  /* now, numeric goal. just check if there's one value
   * tuple satisfying this psi.
   */
  if ( ggoal_psi_id == -1 ) {
    if ( gcmd_line.debug && gcmd_line.dRPG ) {
      printf("\nno num goal!");
    }
    return TRUE;
  }
  if ( !t->psi_VT[ggoal_psi_id]->next ) {    
    if ( gcmd_line.debug && gcmd_line.dRPG ) {
      printf("\nnum goal no!");
    }
    return FALSE;
  }
  if ( gcmd_line.debug && gcmd_line.dRPG ) {
    printf("\nnum goal yes!");
  }
  return TRUE;

}



void RPG_print( void )

{

  RPGlayer *t; 
  RPGfact *p;
  RPGvalue *v;
  RPGvaluetuple *vt;
  RPGaction *a;
  RPGeffect *e;

  RPGactionlist *al;
  RPGeffectlist *el;

  int i, j;

  printf("\n\nRPG:");
  for ( t = gRPG->next; t; t = t->next ) {
    printf("\n\nLayer %d:", t->t);
    printf("\nFacts bits:");
    for ( i = 0; i < gnum_relevant_facts; i++ ) {
      if ( t->is_P[i] ) {
	printf(" %3d", i);
      } else {
	printf("    ");
      }
    }
    printf("\nFacts:");
    for ( p = t->P->next; p; p = p->next ) {
      printf(" (%d: ", p->id);
      print_Fact(p->p);
      printf(")");
    }
    printf("\nFluents:");
    for ( i = 0; i < gnum_relevant_fluents; i++ ) {
      printf("\n%d: ", i);
      print_Fluent(&(grelevant_fluents[i]));
      printf(":");
      for ( v = t->V[i]->next; v; v = v->next ) {
	printf(" %.2f", v->v);
      }
    }

    if ( gcmd_line.debug && gcmd_line.dRPG ) {
      printf("\nConstraint tuples:");
      for ( i = 0; i < gnum_relevant_constraints; i++ ) {
	printf("\n%d: ", i);
	for ( vt = t->constraint_VT[i]->next; vt; vt = vt->next ) {
	  printf("\n");
	  for ( j = 0; j < gnum_relevant_fluents; j++ ) {
	    if ( vt->have[j] ) {
	      printf("%6.2f ", vt->vt[j]);
	    } else {
	      printf("       ");
	    }
	  }
	}
      }

      printf("\nPsi tuples:");
      for ( i = 0; i < gnum_relevant_psis; i++ ) {
	printf("\n%d: ", i);
	for ( vt = t->psi_VT[i]->next; vt; vt = vt->next ) {
	  printf("\n");
	  for ( j = 0; j < gnum_relevant_fluents; j++ ) {
	    if ( vt->have[j] ) {
	      printf("%6.2f ", vt->vt[j]);
	    } else {
	      printf("       ");
	    }
	  }
	}
      }
    }
    
    /* in the last layer built, there are no actions.
     */
    if ( t->A ) {
      printf("\nActions:");
      for ( a = t->A->next; a; a = a->next ) {
	printf("\n%d: ", a->id);
	print_Action_name(a->a);
	printf(":");
	for ( e = a->E->next; e; e = e->next ) {
	  printf(" %d", e->id);
	}
      }


    
      /* connectivity info, for debugging...
       */
      if ( gcmd_line.debug && gcmd_line.dRPG ) {
	printf("\n\nConnectivity:");
	printf("\nFacts:");
	for ( i = 0; i < gnum_relevant_facts; i++ ) {
	  printf("\n\n");
	  print_Fact(&(grelevant_facts[i]));
	  
	  /* added by:
	   */
	  printf("\nAdders: ");
	  for ( el = t->tA[i]->next; el; el = el->next ) {
	    for ( a = t->A->next; a; a = a->next ) {
	      j = 0;
	      for ( e = a->E->next; e; e = e->next ) {
		if ( e == el->e ) {
		  break;
		}
		j++;
	      }
	      if ( e ) {
		break;
	      }
	    }
	    if ( !a ) {
	      printf("\ndidn't find action to effect, print RPG tA?\n\n");
	      exit( 1 );
	    }
	    print_Action_name(a->a);
	    printf("-eff%d, ", j);
	  }
	  
	  /* deleted by:
	   */
	  printf("\nDeleters: ");
	  for ( el = t->tD[i]->next; el; el = el->next ) {
	    for ( a = t->A->next; a; a = a->next ) {
	      j = 0;
	      for ( e = a->E->next; e; e = e->next ) {
		if ( e == el->e ) {
		  break;
		}
		j++;
	      }
	      if ( e ) {
		break;
	      }
	    }
	    if ( !a ) {
	      printf("\ndidn't find action to effect, print RPG tD?\n\n");
	      exit( 1 );
	    }
	    print_Action_name(a->a);
	    printf("-eff%d, ", j);
	  }
	  
	  /* in con of:
	   */
	  printf("\nIn condition of: ");
	  for ( el = t->tC[i]->next; el; el = el->next ) {
	    for ( a = t->A->next; a; a = a->next ) {
	      j = 0;
	      for ( e = a->E->next; e; e = e->next ) {
		if ( e == el->e ) {
		  break;
		}
		j++;
	      }
	      if ( e ) {
		break;
	      }
	    }
	    if ( !a ) {
	      printf("\ndidn't find action to effect, print RPG tC?\n\n");
	      exit( 1 );
	    }
	    print_Action_name(a->a);
	    printf("-eff%d, ", j);
	  }
	  
	  /* in pre of:
	   */
	  printf("\nIn precond of: ");
	  for ( al = t->tP[i]->next; al; al = al->next ) {
	    print_Action_name(al->a->a);
	    printf(",  ");
	  }
	} /* endfor i over fact indices */
	
	printf("\nFluents:");
	for ( i = 0; i < gnum_relevant_fluents; i++ ) {
	  printf("\n\n");
	  print_Fluent(&(grelevant_fluents[i]));
	  
	  /* affected by:
	   */
	  printf("\nAffected by: ");
	  for ( el = t->tXA[i]->next; el; el = el->next ) {
	    for ( a = t->A->next; a; a = a->next ) {
	      j = 0;
	      for ( e = a->E->next; e; e = e->next ) {
		if ( e == el->e ) {
		  break;
		}
		j++;
	      }
	      if ( e ) {
		break;
	      }
	    }
	    if ( !a ) {
	      printf("\ndidn't find action to effect, print RPG tXA?\n\n");
	      exit( 1 );
	    }
	    print_Action_name(a->a);
	    printf("-eff%d, ", j);
	  }
	  
	  /* in con \cup efrhs of:
	   */
	  printf("\nIn con or eff rhs of: ");
	  for ( el = t->tXC[i]->next; el; el = el->next ) {
	    for ( a = t->A->next; a; a = a->next ) {
	      j = 0;
	      for ( e = a->E->next; e; e = e->next ) {
		if ( e == el->e ) {
		  break;
		}
		j++;
	      }
	      if ( e ) {
		break;
	      }
	    }
	    if ( !a ) {
	      printf("\ndidn't find action to effect, print RPG tXC?\n\n");
	      exit( 1 );
	    }
	    print_Action_name(a->a);
	    printf("-eff%d, ", j);
	  }
	  
	  /* in con \cup efrhs of:
	   */
	  printf("\nIn pre of: ");
	  for ( al = t->tXP[i]->next; al; al = al->next ) {
	    print_Action_name(al->a->a);
	    printf(", ");
	  }
	} /* endfor i over fluent indices */
      } /* endif debug */
    } /* endif there is an action layer */
  } /* endfor t over layers */
  fflush(stdout);

}



void RPG_PV_statistics( RPGlayer *t )

{

  RPGfact *p;
  RPGvalue *v;
  RPGvaluetuple *vt;

  int num_p;
  int sum, num;
  int max_v = 0, max_cvt = 0, max_pvt = 0;
  float mean_v, mean_cvt, mean_pvt;
  int i;



  num_p = 0;
  for ( p = t->P->next; p; p = p->next ) num_p++;

  sum = 0;
  for ( i = 0; i < gnum_relevant_fluents; i++ ) {
    num = 0;
    for ( v = t->V[i]->next; v; v = v->next ) {
      sum++;
      num++;
    }
    if ( num > max_v ) {
      max_v = num;
    }
  }
  mean_v = ((float) sum)/((float) gnum_relevant_fluents);

  sum = 0;
  for ( i = 0; i < gnum_relevant_constraints; i++ ) {
    num = 0;
    for ( vt = t->constraint_VT[i]->next; vt; vt = vt->next ) {
      sum++;
      num++;
    }
    if ( num > max_cvt ) {
      max_cvt = num;
    }
  }
  mean_cvt = ((float) sum)/((float) gnum_relevant_constraints);

  sum = 0;
  for ( i = 0; i < gnum_relevant_psis; i++ ) {
    num = 0;
    for ( vt = t->psi_VT[i]->next; vt; vt = vt->next ) {
      sum++;
      num++;
    }
    if ( num > max_pvt ) {
      max_pvt = num;
    }
  }
  mean_pvt = ((float) sum)/((float) gnum_relevant_psis);



  printf("\nRPG layer %d: %d facts", 
	 t->t, num_p);
  printf("\n             %d fluents,     %.2f mean %d max values", 
	 gnum_relevant_fluents, mean_v, max_v);
  printf("\n             %d constraints, %.2f mean %d max satisfying value tuples", 
	 gnum_relevant_constraints, mean_cvt, max_cvt);
  printf("\n             %d psis,        %.2f mean %d max satisfying value tuples", 
	 gnum_relevant_psis, mean_pvt, max_pvt);

  fflush(stdout);

}



void RPG_AE_statistics( RPGlayer *t )

{

  RPGaction *a;
  RPGeffect *e;

  int num_a, num_e;



  num_a = 0;
  num_e = 0;
  if ( t->A ) {
    for ( a = t->A->next; a; a = a->next ) {
      num_a++;
      for ( e = a->E->next; e; e = e->next ) num_e++;
    }
  }



  printf("\nRPG layer %d: %d actions, %d effects", 
	 t->t, num_a, num_e);
  fflush(stdout);

}























/* ------------------------------------------------------------------------------- 
 * utilities for propositional RPG.
 */
























Bool RPG_a_applicable(RPGlayer *t, Action *a)

{

  int i;

  /* first, propositions.
   */
  for ( i = 0; i < a->num_preconds; i++ ) {
    if ( !RPG_P_contains(t, a->preconds[i]) ) {
      if ( gcmd_line.debug && gcmd_line.dRPG ) {
	printf("\nprop applicable no!");
      }
      return FALSE;
    }
  }
  if ( gcmd_line.debug && gcmd_line.dRPG ) {
    printf("\nprop applicable yes!");
  }
  
  /* now, numeric preconds. just check if there's one value
   * tuple satisfying this psi.
   */
  if ( a->pre_psi_id == -1 ) {
    if ( gcmd_line.debug && gcmd_line.dRPG ) {
      printf("\nno num prec!");
    }
    return TRUE;
  }
  if ( !t->psi_VT[a->pre_psi_id]->next ) {    
    if ( gcmd_line.debug && gcmd_line.dRPG ) {
      printf("\nnum applicable no!");
    }
    return FALSE;
  }
  if ( gcmd_line.debug && gcmd_line.dRPG ) {
    printf("\nnum applicable yes!");
  }
  return TRUE;

}



Bool RPG_e_applicable(RPGlayer *t, ActionEffect *e)

{

  int i;

  /* first, propositions.
   */
  for ( i = 0; i < e->num_conditions; i++ ) {
    if ( !RPG_P_contains(t, e->conditions[i]) ) {
      if ( gcmd_line.debug && gcmd_line.dRPG ) {
	printf("\ne prop applicable no!");
      }
      return FALSE;
    }
  }
  if ( gcmd_line.debug && gcmd_line.dRPG ) {
    printf("\ne prop applicable yes!");
  }
    
  /* now, numeric preconds. just check if there's one value
   * tuple satisfying this psi.
   */
  if ( e->con_psi_id == -1 ) {
    if ( gcmd_line.debug && gcmd_line.dRPG ) {
      printf("\ne no num prec+con!");
    }
    return TRUE;
  }
  if ( !t->psi_VT[e->con_psi_id]->next ) {    
    if ( gcmd_line.debug && gcmd_line.dRPG ) {
      printf("\ne num applicable no!");
    }
    return FALSE;
  }
  if ( gcmd_line.debug && gcmd_line.dRPG ) {
    printf("\ne num applicable yes!");
  }
  return TRUE;

}



Bool RPG_P_contains(RPGlayer *t, int id)

{

  return t->is_P[id];

/*   RPGfact *p; */

/*   for ( p = t->P->next; p; p = p->next ) { */
/*     if ( p->id == id ) return TRUE; */
/*   } */

/*   return FALSE; */

}





















/* -------------------------------------------------------------------------------
 * dealing with numeric vars, main functions, ie interfaces to RPGvaluetuples.c
 */





















/* this collects all value tuples in layer t
 * that satisfy constraint id,  and puts them
 * into the RPG entry for the constraint in t,
 * which is assumed to be empty up to this point.
 */
void RPG_get_constraint_valuetuples(RPGlayer *t, int id)

{

  static int *psi;
  static Bool fc = TRUE;

  RPGvaluetuple *vt, *prevvt, *ivt;

  int i, j;



  if ( gcmd_line.debug && gcmd_line.dRPG ) {
    printf("\nget constraint valuetuples id %d.", id);
  }
  /* just double-check, since we sometimes use void ids to say
   * that thre actually is no such thing.
   */
  if ( id == -1 ) {
    printf("\n get tuples for constraint id -1?\n\n");
    exit( 1 );
  }



  /* this probably looks funny; it just serves to
   * create the interface needed for RPG_get_valuetuples.
   * there may be a more elegant solution but who cares...
   */
  if ( fc ) {
    psi = ( int * ) calloc(1, sizeof( int ));
    fc = FALSE;
  }

  psi[0] = id;



  /* this takes in an int aray of constraint ids, and outputs
   * the list of satisfying valuetuples into the list starting with
   * start member gget_valuetuples_result, into the first
   * gget_valuetuples_num_result members.
   */
  RPG_get_valuetuples(t, psi, 1);

  

  /* store this in the RPG. 
   *
   * NOTE: this assumes that this RPG entry is empty right now.
   */
  prevvt = t->constraint_VT[id];
  ivt = gget_valuetuples_result->next;
  for ( i = 0; i < gget_valuetuples_num_result; i++ ) {
    if ( !ivt ) {
      printf("\nleaving allocated valuetuples_result list?\n\n");
      exit( 1 );
    }

    vt = new_RPGvaluetuple();/* have and vt allocated in memory.c */
    for ( j = 0; j < gnum_relevant_fluents; j++ ) {
      vt->have[j] = ivt->have[j];
      vt->vt[j] = ivt->vt[j];
    }
    if ( gcmd_line.debug && gcmd_line.dRPG ) {
      printf("\nstored valuetuple for constraint %d: ", id);      
      for ( j = 0; j < gnum_relevant_fluents; j++ ) {
	if ( vt->have[j] ) {
	  printf(" %6.2f", vt->vt[j]);
	} else {
	  printf("       ");
	}
      }
    }

    vt->prev = prevvt;
    prevvt->next = vt;
    prevvt = vt;

    ivt = ivt->next;
  }

}





/* this collects all value tuples in layer t
 * that satisfy psi id,  and puts them
 * into the RPG entry for the constraint in t,
 * which is assumed to be empty up to this point.
 */
void RPG_get_psi_valuetuples(RPGlayer *t, int id)

{

  RPGvaluetuple *vt, *prevvt, *ivt;

  int i, j;



  if ( gcmd_line.debug && gcmd_line.dRPG ) {
    printf("\nget psi valuetuples id %d.", id);
  }
  if ( id == -1 ) {
    printf("\n get tuples for psi id -1?\n\n");
    exit( 1 );
  }



  RPG_get_valuetuples(t, 
		      grelevant_psis[id]->psi, 
		      grelevant_psis[id]->num_psi);



  prevvt = t->psi_VT[id];
  ivt = gget_valuetuples_result->next;
  for ( i = 0; i < gget_valuetuples_num_result; i++ ) {
    if ( !ivt ) {
      printf("\nleaving allocated valuetuples_result list?\n\n");
      exit( 1 );
    }

    vt = new_RPGvaluetuple();
    for ( j = 0; j < gnum_relevant_fluents; j++ ) {
      vt->have[j] = ivt->have[j];
      vt->vt[j] = ivt->vt[j];
    }
    if ( gcmd_line.debug && gcmd_line.dRPG ) {
      printf("\nstored valuetuple for psi %d: ", id);      
      for ( j = 0; j < gnum_relevant_fluents; j++ ) {
	if ( vt->have[j] ) {
	  printf(" %6.2f", vt->vt[j]);
	} else {
	  printf("       ");
	}
      }
    }

    vt->prev = prevvt;
    prevvt->next = vt;
    prevvt = vt;

    ivt = ivt->next;
  }

}



/* this collects all values of (lhs type rhs) in t that come from
 * valuetuples consistent
 * with at least one valuetuple of (psi id) in t. the values are
 * then inserted into the values of lhs in tpp.
 */
void RPG_insert_effect(RPGlayer *t,
		       int id,
		       int lhs,
		       NumericEffectType type,
		       ExpNode *rhs)
{

  static ExpNode *exp, *lhsnode;
  static Bool fc = TRUE;

  RPGlayer *tpp = t->next;
  RPGvalue *prevv, *iv, *jv;

  int i;



  if ( gcmd_line.debug && gcmd_line.dRPG ) {
    printf("\ninsert effect id %d, lhs %d.", id, lhs);
  }
  if ( fc ) {
    /* conn here doesn't matter.
     */
    exp = new_ExpNode( FHEAD );
    /* here it does: this will contain lhs fluent if needed.
     */
    lhsnode = new_ExpNode( FHEAD );
    /* will always be on the exp lhs, if needed.
     */
    exp->leftson = lhsnode;

    fc = FALSE;
  }



  /* assemble exp: normalize to ":=" effects.
   *
   * NOTE: this is important in the sense that it introduces
   * an additional variable into the effect right hand side.
   * without the normalization, we'd have to enumerate
   * the values for this var separately.
   *
   * remember that exp->leftson was set above already.
   */
  if ( !rhs ) {
    printf("\ngetting values for an empty rhs?\n\n");
    exit( 1 );
  } 
  switch ( type ) {
  case SCALE_UP:
    lhsnode->fl = lhs;
    exp->connective = MU;
    exp->rightson = rhs;
    break;
  case SCALE_DOWN:
    lhsnode->fl = lhs;
    exp->connective = DI;
    exp->rightson = rhs;
    break;
  case INCREASE:
    lhsnode->fl = lhs;
    exp->connective = AD;
    exp->rightson = rhs;
    break;
  case DECREASE:
    lhsnode->fl = lhs;
    exp->connective = SU;
    exp->rightson = rhs;
    break;
  case ASSIGN:
    /* here, rhs actually is the expression we're looking for.
     */
    break;
  default:
    printf("\nillegal numeric effect type!\n\n");
    exit( 1 );
  }



  /* takes a psi id (may be -1) and an expression in bar{x},
   * and outs synchronized lists of bar{x} value tuples and values,
   * with the meaning that value[i] arises for exp under valuetuple[i].
   * the tuples are all in this layer that are in agreement with at least
   * one tuple satisfying psi.
   * relies on that the value tuples for psi are assembled 
   * in the RPG layer already.
   */
  if ( type != ASSIGN ) {
    RPG_get_valuetuples_exp(t, id, exp);
  } else {
    RPG_get_valuetuples_exp(t, id, rhs);
  }



  /* for our purposes here, we don't actually *need* the valuetuples
   * -- these will be needed for the CNF only.
   *
   * we just take all the values and add them into the values of
   * lhs in tpp. ATTENTION! we have to check for duplicates.
   * the list may contain entries with different variable value
   * tuples, but identical expression outcome values. all the
   * tuples are needed for the CNF, but here only the outcome values matter.
   */
  if ( !tpp || !tpp->V ) {
    printf("\ntpp to insert values into not there?\n\n");
    exit( 1 );
  }
  iv = gget_valuetuples_exp_result_v->next;
  for ( i = 0; i < gget_valuetuples_exp_num_result; i++ ) {
    if ( !iv ) {
      printf("\nleaving allocated valuetuples_exp_result v list?\n\n");
      exit( 1 );
    }

    /* check if we got this already; at the same time get last 
     * element into prevv.
     */
    if ( gcmd_line.debug && gcmd_line.dRPG ) {
      printf("\ntry value for effect id %d, lhs %d: %.2f", id, lhs, iv->v);
    }
    prevv = tpp->V[lhs];
    for ( jv = tpp->V[lhs]->next; jv; jv = jv->next ) {
      if ( jv->v == iv->v ) {
	break;
      }
      prevv = jv;
    }
    if ( jv ) {
      /* had this! skip.
       */
      if ( gcmd_line.debug && gcmd_line.dRPG ) {
	printf(" have that!");
      }
      iv = iv->next;
      continue;
    }
    if ( gcmd_line.debug && gcmd_line.dRPG ) {
      printf(" don't have that!");
    }

    jv = new_RPGvalue();
    jv->v = iv->v;
    jv->prev = prevv;
    prevv->next = jv;

    iv = iv->next;
  }

}























/* -------------------------------------------------------------------------------
 * connectivity info.
 */






















void RPG_get_connectivity( RPGlayer *t )

{

  RPGaction *a;
  RPGeffect *e;

  RPGeffectlist *el;
  RPGactionlist *al;

  int i, j;



  /* initialize all these lists.
   */
  t->tA = ( RPGeffectlist_pointer * ) calloc(gnum_relevant_facts, sizeof( RPGeffectlist * ) );
  t->tendA = ( RPGeffectlist_pointer * ) calloc(gnum_relevant_facts, sizeof( RPGeffectlist * ) );
  t->tD = ( RPGeffectlist_pointer * ) calloc(gnum_relevant_facts, sizeof( RPGeffectlist * ) );
  t->tendD = ( RPGeffectlist_pointer * ) calloc(gnum_relevant_facts, sizeof( RPGeffectlist * ) );
  t->tC = ( RPGeffectlist_pointer * ) calloc(gnum_relevant_facts, sizeof( RPGeffectlist * ) );
  t->tendC = ( RPGeffectlist_pointer * ) calloc(gnum_relevant_facts, sizeof( RPGeffectlist * ) );
  t->tP = ( RPGactionlist_pointer * ) calloc(gnum_relevant_facts, sizeof( RPGactionlist * ) );
  t->tendP = ( RPGactionlist_pointer * ) calloc(gnum_relevant_facts, sizeof( RPGactionlist * ) );
  t->tXA = ( RPGeffectlist_pointer * ) calloc(gnum_relevant_fluents, sizeof( RPGeffectlist * ) );
  t->tendXA = ( RPGeffectlist_pointer * ) calloc(gnum_relevant_fluents, sizeof( RPGeffectlist * ) );
  t->tXC = ( RPGeffectlist_pointer * ) calloc(gnum_relevant_fluents, sizeof( RPGeffectlist * ) );
  t->tendXC = ( RPGeffectlist_pointer * ) calloc(gnum_relevant_fluents, sizeof( RPGeffectlist * ) );
  t->tXP = ( RPGactionlist_pointer * ) calloc(gnum_relevant_fluents, sizeof( RPGactionlist * ) );
  t->tendXP = ( RPGactionlist_pointer * ) calloc(gnum_relevant_fluents, sizeof( RPGactionlist * ) );
  for ( i = 0; i < gnum_relevant_facts; i++ ) {
    t->tA[i] = new_RPGeffectlist();
    t->tendA[i] = t->tA[i];
    t->tD[i] = new_RPGeffectlist();
    t->tendD[i] = t->tD[i];
    t->tC[i] = new_RPGeffectlist();
    t->tendC[i] = t->tC[i];
    t->tP[i] = new_RPGactionlist();
    t->tendP[i] = t->tP[i];
  }
  for ( i = 0; i < gnum_relevant_fluents; i++ ) {
    t->tXA[i] = new_RPGeffectlist();
    t->tendXA[i] = t->tXA[i];
    t->tXC[i] = new_RPGeffectlist();
    t->tendXC[i] = t->tXC[i];
    t->tXP[i] = new_RPGactionlist();
    t->tendXP[i] = t->tXP[i];
  }



  /* now just walk once through all actions and effects, and
   * fill the lists.
   */
  for ( a = t->A->next; a; a = a->next ) {

    /* preconds.
     */
    for ( i = 0; i < a->a->num_preconds; i++ ) {
      al = new_RPGactionlist();
      al->a = a;
      t->tendP[a->a->preconds[i]]->next = al;
      al->prev = t->tendP[a->a->preconds[i]];
      t->tendP[a->a->preconds[i]] = al;
    }
    for ( i = 0; i < a->a->num_numeric_preconds; i++ ) {
      /* this inserts list els into XP for all fluents that occur in here.
       */
      RPG_get_connectivity_a_exp(t, a, a->a->numeric_preconds_lh[i]);
      RPG_get_connectivity_a_exp(t, a, a->a->numeric_preconds_rh[i]);
    }

    /* effects.
     */
    for ( e = a->E->next; e; e = e->next ) {

      /* conditions.
       */
      for ( i = 0; i < e->e->num_conditions; i++ ) {
	el = new_RPGeffectlist();
	el->e = e;
	t->tendC[e->e->conditions[i]]->next = el;
	el->prev = t->tendC[e->e->conditions[i]];
	t->tendC[e->e->conditions[i]] = el;
      }
      for ( i = 0; i < e->e->num_numeric_conditions; i++ ) {
	/* this inserts list els into XC for all fluents that occur in here.
	 */
	RPG_get_connectivity_e_exp(t, e, e->e->numeric_conditions_lh[i]);
	RPG_get_connectivity_e_exp(t, e, e->e->numeric_conditions_rh[i]);
      }
      /* effect right hand sides: also go into the XC lists, since interference
       * criterion will be the same: e' must not affect any var used by e in con \cup rhsides
       */
      for ( i = 0; i < e->e->num_numeric_effects; i++ ) {
	RPG_get_connectivity_e_exp(t, e, e->e->numeric_effects_rh[i]);
      }

      /* adds
       */
      for ( i = 0; i < e->e->num_adds; i++ ) {
	el = new_RPGeffectlist();
	el->e = e;
	t->tendA[e->e->adds[i]]->next = el;
	el->prev = t->tendA[e->e->adds[i]];
	t->tendA[e->e->adds[i]] = el;
      }

      /* dels
       */
      for ( i = 0; i < e->e->num_dels; i++ ) {
	el = new_RPGeffectlist();
	el->e = e;
	t->tendD[e->e->dels[i]]->next = el;
	el->prev = t->tendD[e->e->dels[i]];
	t->tendD[e->e->dels[i]] = el;
      }

      /* effect left hand sides. into XA.
       * double check at this point that no effect
       * affects the same x twice.
       */
      for ( i = 0; i < e->e->num_numeric_effects-1; i++ ) {
	for ( j = i+1; j < e->e->num_numeric_effects; j++ ) {
	  if ( e->e->numeric_effects_fl[i] == e->e->numeric_effects_fl[j] ) {
	    printf("\naction ");
	    print_Action_name(a->a);
	    printf(" effect affects ");
	    print_Fluent(&(grelevant_fluents[e->e->numeric_effects_fl[i]]));
	    printf(" twice? check input files.\n\n");
	    exit( 0 );
	  }
	}
      }
      for ( i = 0; i < e->e->num_numeric_effects; i++ ) {
	el = new_RPGeffectlist();
	el->e = e;
	t->tendXA[e->e->numeric_effects_fl[i]]->next = el;
	el->prev = t->tendXA[e->e->numeric_effects_fl[i]];
	t->tendXA[e->e->numeric_effects_fl[i]] = el;
      }
    } /* endfor e over effects */
  } /* endfor a over actions in t */

}



/* this inserts list els into XP for all fluents that occur in here.
 */
void RPG_get_connectivity_a_exp( RPGlayer *t, RPGaction *a, ExpNode *exp )

{

  RPGactionlist *al;

  if ( !exp ) {
    printf("\nwarning: get a connectivity in an empty expression?");
    return;
  }

  switch ( exp->connective ) {
  case FHEAD:
    if ( exp->fl < 0 ) {
      printf("\nfl < 0 in get conn a exp?\n\n");
      exit( 1 );
    }
    /* here we must make duplicate checking, since the same fluent may
     * appear twice in an action precondition.
     */
    for ( al = t->tXP[exp->fl]->next; al; al = al->next ) {
      if ( al->a == a ) {
	break;
      }
    }
    if ( al ) {
      break;
    }
    al = new_RPGactionlist();
    al->a = a;
    t->tendXP[exp->fl]->next = al;
    al->prev = t->tendXP[exp->fl];
    t->tendXP[exp->fl] = al;
    break;
  case NUMBER:
    break;
  case MINUS:
    RPG_get_connectivity_a_exp(t, a, exp->son);
    break;
  case AD:
  case SU:
  case MU:
  case DI:
    RPG_get_connectivity_a_exp(t, a, exp->leftson);
    RPG_get_connectivity_a_exp(t, a, exp->rightson);
    break;
  default:
    printf("\nwrong connective in get conn a exp?\n\n");
    exit( 1 );
  }

}



/* this inserts list els into XC for all fluents that occur in here.
 */
void RPG_get_connectivity_e_exp( RPGlayer *t, RPGeffect *e, ExpNode *exp )

{

  RPGeffectlist *el;

  if ( !exp ) {
    printf("\nwarning: get e connectivity in an empty expression?");
    return;
  }

  switch ( exp->connective ) {
  case FHEAD:
    if ( exp->fl < 0 ) {
      printf("\nfl < 0 in get conn e exp?\n\n");
      exit( 1 );
    }
    /* here we must make duplicate checking, since the same fluent may
     * appear twice in an effect condition/eff rhsides.
     */
    for ( el = t->tXC[exp->fl]->next; el; el = el->next ) {
      if ( el->e == e ) {
	break;
      }
    }
    if ( el ) {
      break;
    }
    el = new_RPGeffectlist();
    el->e = e;
    t->tendXC[exp->fl]->next = el;
    el->prev = t->tendXC[exp->fl];
    t->tendXC[exp->fl] = el;
    break;
  case NUMBER:
    break;
  case MINUS:
    RPG_get_connectivity_e_exp(t, e, exp->son);
    break;
  case AD:
  case SU:
  case MU:
  case DI:
    RPG_get_connectivity_e_exp(t, e, exp->leftson);
    RPG_get_connectivity_e_exp(t, e, exp->rightson);
    break;
  default:
    printf("\nwrong connective in get conn e exp?\n\n");
    exit( 1 );
  }

}

