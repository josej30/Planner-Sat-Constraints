
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
 * File: RPGvaluetuples.c
 * Description: functions dealing with RPG value tuples.
 *              made global since will (?) also be accessed by CNF builder.
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
 * locally globally needed data structures.
 */

















#define RPG_MAXRECDEPTH 1000



/* overall output
 */
RPGvaluetuple_pointer lrecd_VT[RPG_MAXRECDEPTH];/* pointers to start elements */
RPGvalue_pointer lrecd_V[RPG_MAXRECDEPTH];
int lnum_recd[RPG_MAXRECDEPTH];



/* intermediate storage of lhs in +,-,*,/
 */
RPGvaluetuple_pointer lrecd_lhs_VT[RPG_MAXRECDEPTH];
RPGvalue_pointer lrecd_lhs_V[RPG_MAXRECDEPTH];
int lnum_recd_lhs[RPG_MAXRECDEPTH];




















/* -------------------------------------------------------------------------------
 * main overlooking functions.
 */



















/* this takes in an int array of constraint ids, and outputs
 * the list of satisfying valuetuples into the list starting with
 * start member gget_valuetuples_result, into the first
 * gget_valuetuples_num_result members.
 *
 * in difference to RPG_get_valuetuples_exp, this takes
 * a list of constraints, not a psi id; reason: this fn
 * is used to compute the constraint and psi extensions in
 * the first place, so a psi id is just a shorthand for
 * a constraint set, with nothing gained.
 *
 *
 * method: call RPG_get_VT_and_V
 * with don't-care vt on the lhs of the first constraint;
 * do the same with the rhs; take all pairs of tuples;
 * skip those that contradict or whose values do not 
 * satisfy the constraint. merge the tuples for each of the others.
 * store the result and do the same for the 2nd constraint.
 * merge the outcome with the stored previous results,
 * by taking all pairs and skipping those that contradict.
 * (corresponds to database join operator). iterate.
 *
 * easy except for storage handling. we'll do this:
 *
 * tuplestores, herein:
 *    lhs
 *    now
 *    res
 *
 * tuplestores, interfaces:
 *    getresult: result of RPG_get_VT_and_V
 *    result: our own output
 *
 * method:
 * for all constraints c
 *    get lhs(c)
 *    copy getresult to lhs
 *    get rhs(c)
 *    if first c
 *      merge lhs, getresult to result
 *    else
 *      merge lhs, getresult to now
 *      merge result, now to res
 *      copy res to result
 *    endif
 * endfor 
 */
void RPG_get_valuetuples(RPGlayer *t,
			 int *psi,
			 int num_psi)

{

  static Bool fc = TRUE;

  /* this is just our void guy to use for RPG_get_VT_and_V
   */
  static RPGvaluetuple *vt;

  /* these are our local stores, see above!
   * lhs is the only one that is concerned with evaluating
   * constraints, so there we also need the *values*.
   */
  static RPGvaluetuple *lhsvt, *now, *res;
  static RPGvalue *lhsv;

  /* these guys will serve to store the merged valuevector
   * before inserting it into the output data structure.
   */
  static Bool *reshave;
  static float *resvt;

  RPGvaluetuple *jvt, *kvt, *gvt, *prevvt;
  RPGvalue *jv, *kv, *prevv;

  RPGvaluetuple *current_end;

  int num_lhs, num_now, num_res;
  int i, j, k, l;



  if ( fc ) {
    gget_valuetuples_result = new_RPGvaluetuple();

    lhsvt = new_RPGvaluetuple();
    lhsv = new_RPGvalue();
    now = new_RPGvaluetuple();
    res = new_RPGvaluetuple();

    /* this will be initialized in memory.c to what we want:
     * don't care all over the place.
     */
    vt = new_RPGvaluetuple();

    reshave = ( Bool * ) calloc(gnum_relevant_fluents, sizeof( Bool ));
    resvt = ( float * ) calloc(gnum_relevant_fluents, sizeof( float ));

    fc = FALSE;
  }



  /* for i over all constraints c
   */
  for ( i = 0; i < num_psi; i++ ) {



    /* get lhs(c)
     */
    RPG_get_VT_and_V(0, t, vt, grelevant_constraints_lhs[psi[i]]);
    


    /* copy getresult to lhs
     */
    jvt = lhsvt->next;
    prevvt = lhsvt;
    jv = lhsv->next;
    prevv = lhsv;
    kvt = lrecd_VT[0]->next;
    kv = lrecd_V[0]->next;
    for ( k = 0; k < lnum_recd[0]; k++ ) {
      if ( !kvt || !kv ) {
	printf("\nleaving kvt/kv getresult allocation in 1, get_valuetuples?\n\n");
	exit( 1 );
      }
      if ( !jvt ) {
	jvt = new_RPGvaluetuple();
	jvt->prev = prevvt;
	prevvt->next = jvt;
      }
      for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	jvt->have[l] = kvt->have[l];
	jvt->vt[l] = kvt->vt[l];
      }
      if ( !jv ) {
	jv = new_RPGvalue();
	jv->prev = prevv;
	prevv->next = jv;
      }
      jv->v = kv->v;
      prevvt = jvt;
      jvt = jvt->next;
      prevv = jv;
      jv = jv->next;
      kvt = kvt->next;
      kv = kv->next;
    } /* endfor jvt, jv, kvt, kv, k copy getresult to lhs */
    num_lhs = lnum_recd[0];



    /* get rhs(c)
     */
    RPG_get_VT_and_V(0, t, vt, grelevant_constraints_rhs[psi[i]]);
    


    /* if first c
     */
    if ( i == 0 ) {



      /* merge lhs, getresult to result
       */
      gget_valuetuples_num_result = 0;
      current_end = gget_valuetuples_result;
      /* here we'd normally also just keep prevp uptodate
       * to the last element;
       * right now we find this during a debug loop, see below.
       */
      /* jvt, jv, j over lhs
       */
      jvt = lhsvt->next;
      jv = lhsv->next;
      for ( j = 0; j < num_lhs; j++ ) {
	if ( !jvt || !jv ) {
	  printf("\nleaving jvt/jv lhs allocation in 1, get_valuetuples?\n\n");
	  exit( 1 );
	}
	/* kvt, kv, k over getresult
	 */
	kvt = lrecd_VT[0]->next;
	kv = lrecd_V[0]->next;
	for ( k = 0; k < lnum_recd[0]; k++ ) {
	  if ( !kvt || !kv ) {
	    printf("\nleaving kvt/kv getresult allocation in 2, get_valuetuples?\n\n");
	    exit( 1 );
	  }

	  /* if these values don't satisfy c: next k.
	   */
	  if ( !number_comparison_holds(grelevant_constraints_comp[psi[i]],
					jv->v, kv->v) ) {
	    kvt = kvt->next;
	    kv = kv->next;
	    continue;
	  }

	  /* check for contradiction, and assemble reshave, resvt
	   */
	  for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	    if ( jvt->have[l] && kvt->have[l] && jvt->vt[l] != kvt->vt[l] ) {
	      break;
	    }
	    if ( jvt->have[l] ) {
	      reshave[l] = TRUE;
	      resvt[l] = jvt->vt[l];
	      continue;
	    }
	    if ( kvt->have[l] ) {
	      reshave[l] = TRUE;
	      resvt[l] = kvt->vt[l];
	      continue;
	    }
	    reshave[l] = FALSE;
	    resvt[l] = -1;
	  }
	  if ( l < gnum_relevant_fluents ) {
	    kvt = kvt->next;
	    kv = kv->next;
	    continue;
	  }

	  gvt = current_end->next;
	  if ( !gvt ) {
	    gvt = new_RPGvaluetuple();
	    gvt->prev = current_end;
	    current_end->next = gvt;
	  }
	  current_end = gvt;
	  for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	    gvt->have[l] = reshave[l];
	    gvt->vt[l] = resvt[l];
	  }
	  gget_valuetuples_num_result++;

	  kvt = kvt->next;
	  kv = kv->next;
	} /* endfor kvt, kv, k over getresult: merge lhs, getresult to result */

	jvt = jvt->next;
	jv = jv->next;
      } /* endfor jvt, jv, j over lhs: merge lhs, getresult to result */
    } else {
      /* NOT the first constraint
       */



      /* merge lhs, getresult to now
       */
      num_now = 0;
      current_end = now;
      jvt = lhsvt->next;
      jv = lhsv->next;
      for ( j = 0; j < num_lhs; j++ ) {
	if ( !jvt || !jv ) {
	  printf("\nleaving jvt/jv lhs allocation in 2, get_valuetuples?\n\n");
	  exit( 1 );
	}
	kvt = lrecd_VT[0]->next;
	kv = lrecd_V[0]->next;
	for ( k = 0; k < lnum_recd[0]; k++ ) {
	  if ( !kvt || !kv ) {
	    printf("\nleaving kvt/kv getresult allocation in 3, get_valuetuples?\n\n");
	    exit( 1 );
	  }
	  if ( !number_comparison_holds(grelevant_constraints_comp[psi[i]],
					jv->v, kv->v) ) {
	    kvt = kvt->next;
	    kv = kv->next;
	    continue;
	  }
	  for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	    if ( jvt->have[l] && kvt->have[l] && jvt->vt[l] != kvt->vt[l] ) {
	      break;
	    }
	    if ( jvt->have[l] ) {
	      reshave[l] = TRUE;
	      resvt[l] = jvt->vt[l];
	      continue;
	    }
	    if ( kvt->have[l] ) {
	      reshave[l] = TRUE;
	      resvt[l] = kvt->vt[l];
	      continue;
	    }
	    reshave[l] = FALSE;
	    resvt[l] = -1;
	  }
	  if ( l < gnum_relevant_fluents ) {
	    kvt = kvt->next;
	    kv = kv->next;
	    continue;
	  }
	  gvt = current_end->next;
	  if ( !gvt ) {
	    gvt = new_RPGvaluetuple();
	    gvt->prev = current_end;
	    current_end->next = gvt;
	  }
	  current_end = gvt;
	  for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	    gvt->have[l] = reshave[l];
	    gvt->vt[l] = resvt[l];
	  }
	  num_now++;
	  kvt = kvt->next;
	  kv = kv->next;
	} /* endfor kvt, kv, k over getresult: merge lhs, getresult to now */
	jvt = jvt->next;
	jv = jv->next;
      } /* endfor jvt, jv, j over lhs: merge lhs, getresult to now */

 

      /* merge result, now to res
       */
      num_res = 0;
      current_end = res;
      jvt = gget_valuetuples_result->next;
      for ( j = 0; j < gget_valuetuples_num_result; j++ ) {
	if ( !jvt ) {
	  printf("\nleaving jvt lhs allocation in 3, get_valuetuples?\n\n");
	  exit( 1 );
	}
	kvt = now->next;
	for ( k = 0; k < num_now; k++ ) {
	  if ( !kvt ) {
	    printf("\nleaving kvt getresult allocation in 4, get_valuetuples?\n\n");
	    exit( 1 );
	  }
	  for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	    if ( jvt->have[l] && kvt->have[l] && jvt->vt[l] != kvt->vt[l] ) {
	      break;
	    }
	    if ( jvt->have[l] ) {
	      reshave[l] = TRUE;
	      resvt[l] = jvt->vt[l];
	      continue;
	    }
	    if ( kvt->have[l] ) {
	      reshave[l] = TRUE;
	      resvt[l] = kvt->vt[l];
	      continue;
	    }
	    reshave[l] = FALSE;
	    resvt[l] = -1;
	  }
	  if ( l < gnum_relevant_fluents ) {
	    kvt = kvt->next;
	    continue;
	  }
	  gvt = current_end->next;
	  if ( !gvt ) {
	    gvt = new_RPGvaluetuple();
	    gvt->prev = current_end;
	    current_end->next = gvt;
	  }
	  current_end = gvt;
	  for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	    gvt->have[l] = reshave[l];
	    gvt->vt[l] = resvt[l];
	  }
	  num_res++;
	  kvt = kvt->next;
	} /* endfor kvt, k over getresult: merge result, now to res */
	jvt = jvt->next;
      } /* endfor jvt, j over lhs: merge result, now to res */



      /* copy res to result
       */
      jvt = gget_valuetuples_result->next;
      prevvt = gget_valuetuples_result;
      kvt = res->next;
      for ( k = 0; k < num_res; k++ ) {
	if ( !kvt ) {
	  printf("\nleaving kvt res allocation in 5, get_valuetuples?\n\n");
	  exit( 1 );
	}
	if ( !jvt ) {
	  jvt = new_RPGvaluetuple();
	  jvt->prev = prevvt;
	  prevvt->next = jvt;
	}
	for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	  jvt->have[l] = kvt->have[l];
	  jvt->vt[l] = kvt->vt[l];
	}
	prevvt = jvt;
	jvt = jvt->next;
	kvt = kvt->next;
      } /* endfor jvt, jv, kvt, kv, k copy getresult to lhs */
      gget_valuetuples_num_result = num_res;

    } /* endif i == 0 ie first constraint or not */
  } /* endfor i over all constraints c */

}



/* takes a psi id and an expression in bar{x},
 * and outs synchronized lists of bar{x} value tuples and values,
 * with the meaning that value[i] arises for exp under valuetuple[i].
 * the tuples are all in this layer that are in agreement with at least
 * one tuple satisfying psi.
 * relies on that the value tuples for psi are assembled 
 * in the RPG layer already.
 *
 * output:
 * extern RPGvaluetuple *gget_valuetuples_exp_result_vt;
 * extern RPGvalue *gget_valuetuples_exp_result_v;
 * extern int gget_valuetuples_exp_num_result;
 *
 * psi id may be -1.
 *
 * in difference to RPG_get_valuetuples, this takes
 * a psi id, not a list of constraints; reason: this fn
 * will be used *after* the psi extensions have been done in the
 * RPG, so these need only be looked up there, for the entire psi.
 *
 *
 * method: iteratively call RPG_get_VT_and_V
 * on all valuetuples in the extension of psi[id];
 * take the union of the results.
 */
void RPG_get_valuetuples_exp(RPGlayer *t,
			     int id,
			     ExpNode *exp)

{

  static Bool fc = TRUE;
  /* this is just our void guy to use for RPG_get_VT_and_V in case psi is -1
   */
  static RPGvaluetuple *vt;

  RPGvaluetuple *ivt, *jvt, *kvt, *prevvt;
  RPGvalue *jv, *kv, *prevv;

  int j, k, l;



  if ( fc ) {
    gget_valuetuples_exp_result_vt = new_RPGvaluetuple();
    gget_valuetuples_exp_result_v = new_RPGvalue();

    /* this will be initialized in memory.c to what we want:
     * don't care all over the place.
     */
    vt = new_RPGvaluetuple();

    fc = FALSE;
  }



  /* initialize the result, ie set to empty set. that's it.
   */
  gget_valuetuples_exp_num_result = 0;

  if ( id != -1 ) {
    /* for ivt over all value tuples in t that satisfy psi
     */
    for ( ivt = t->psi_VT[id]->next; ivt; ivt = ivt->next ) {
      
      /* call RPG_get_VT_and_V. this will write the result into
       * RPGvaluetuple_pointer lrecd_VT[0];
       * RPGvalue_pointer lrecd_V[0];
       * int lnum_recd[0];
       */
      RPG_get_VT_and_V(0, t, ivt, exp);
      
      /* append this to gget_valuetuples_exp_result_v(t).
       * check for duplicates.
       *
       * INEFFICIENT: if e.g. exp and psi don't share any variables
       *              then for each tuple in the psi extension the exact same thing
       *              will be done. maybe find a solution to this
       *              later, if RPG runtime is relevant.
       */
      
      /* for jvt, jv over all tuples and values in the RPG_get_VT_and_V output
       */
      jvt = lrecd_VT[0]->next;
      jv = lrecd_V[0]->next;
      for ( j = 0; j < lnum_recd[0]; j++ ) {
	if ( !jvt || !jv ) {
	  printf("\nleaving allocated jvt/jv space at get exp_result?\n\n");
	  exit( 1 );
	}
	
	/* for kvt, kv over all we got so far
	 */
	kvt = gget_valuetuples_exp_result_vt->next;
	prevvt = gget_valuetuples_exp_result_vt;
	kv = gget_valuetuples_exp_result_v->next;
	prevv = gget_valuetuples_exp_result_v;
	for ( k = 0; k < gget_valuetuples_exp_num_result; k++ ) {
	  if ( !kvt || !kv ) {
	    printf("\nleaving allocated kvt/kv space at get exp_result?\n\n");
	    exit( 1 );
	  }
	  
	  /* is value vector the same?
	   */
	  for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	    if ( jvt->have[l] != kvt->have[l] ) {
	      printf("\njvt and kvt talk about different variables at get exp_result?\n\n");
	      exit( 1 );
	    }
	    if ( jvt->vt[l] != kvt->vt[l] ) {
	      break;
	    }
	  }
	  if ( l == gnum_relevant_fluents ) {
	    /* value vector is the same! skip.
	     */
	    if ( jv->v != kv->v ) {
	      /* if var values are the same, exp value should also be the same!
	       */
	      printf("\njvt and kvt same but values diff at get exp_result?\n\n");
	      exit( 1 );
	    }
	    /* stop going along what we have so far.
	     */
	    break;
	  }
	  
	  prevvt = kvt;
	  kvt = kvt->next;
	  prevv = kv;
	  kv = kv->next;
	} /* endfor kvt, kv, k over tuples/values we got so far */
	
	if ( k < gget_valuetuples_exp_num_result ) {
	  /* this jvt, jv is a duplicate! skip.
	   */
	  jvt = jvt->next;
	  jv = jv->next;
	  continue;
	}
	
	/* now out tuple/value is new, and our desired output list end
	 * is in prevvt->next = kvt, prevv->next = kv.
	 */
	if ( !kvt ) {
	  kvt = new_RPGvaluetuple();
	  kvt->prev = prevvt;
	  prevvt->next = kvt;
	}
	for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	  kvt->have[l] = jvt->have[l];
	  kvt->vt[l] = jvt->vt[l];
	}
	
	if ( !kv ) {
	  kv = new_RPGvalue();
	  kv->prev = prevv;
	  prevv->next = kv;
	}
	kv->v = jv->v;
	
	gget_valuetuples_exp_num_result++;
	
	jvt = jvt->next;
	jv = jv->next;
      } /* endfor jvt, jv, j over tuples/values returned by RPG_get_VT_and_V for this vt */
      
      /* the ivt loop is a normal 1-pointer loop so no stuff at its end. */
    } /* endfor ivt over all tuples vt that satisfy psi at layer t */

    return;
  } /* endif psi != -1 */



  /* now, if psi == -1, then just do one iteration of the i-loop,
   * using the don't-care vt to constrain  RPG_get_VT_and_V;
   */
  RPG_get_VT_and_V(0, t, vt, exp);
  jvt = lrecd_VT[0]->next;
  jv = lrecd_V[0]->next;
  for ( j = 0; j < lnum_recd[0]; j++ ) {
    if ( !jvt || !jv ) {
      printf("\nleaving allocated jvt/jv space at get exp_result?\n\n");
      exit( 1 );
    }
    kvt = gget_valuetuples_exp_result_vt->next;
    prevvt = gget_valuetuples_exp_result_vt;
    kv = gget_valuetuples_exp_result_v->next;
    prevv = gget_valuetuples_exp_result_v;
    for ( k = 0; k < gget_valuetuples_exp_num_result; k++ ) {
      if ( !kvt || !kv ) {
	printf("\nleaving allocated kvt/kv space at get exp_result?\n\n");
	exit( 1 );
      }
      for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	if ( jvt->have[l] != kvt->have[l] ) {
	  printf("\njvt and kvt talk about different variables at get exp_result?\n\n");
	  exit( 1 );
	}
	if ( jvt->vt[l] != kvt->vt[l] ) {
	  break;
	}
      }
      if ( l == gnum_relevant_fluents ) {
	if ( jv->v != kv->v ) {
	  printf("\njvt and kvt same but values diff at get exp_result?\n\n");
	  exit( 1 );
	}
	break;
      }
      prevvt = kvt;
      kvt = kvt->next;
      prevv = kv;
      kv = kv->next;
    } /* endfor kvt, kv, k over tuples/values we got so far */
    if ( k < gget_valuetuples_exp_num_result ) {
      jvt = jvt->next;
      jv = jv->next;
      continue;
    }
    if ( !kvt ) {
      kvt = new_RPGvaluetuple();
      kvt->prev = prevvt;
      prevvt->next = kvt;
    }
    for ( l = 0; l < gnum_relevant_fluents; l++ ) {
      kvt->have[l] = jvt->have[l];
      kvt->vt[l] = jvt->vt[l];
    }
    if ( !kv ) {
      kv = new_RPGvalue();
      kv->prev = prevv;
      prevv->next = kv;
    }
    kv->v = jv->v;
    gget_valuetuples_exp_num_result++;
    jvt = jvt->next;
    jv = jv->next;
  } /* endfor jvt, jv, j over tuples/values returned by RPG_get_VT_and_V for this vt */

}























/* ------------------------------------------------------------------------------- 
 * the technical core functions.
 */






















/* the next one is the essential gathering function. given:
 *
 * a value tuple vt (which may be totally "don't care"), and
 * an expression exp, 
 *
 * it outputs synchronized lists containing:
 *
 * the set of value tuples that instantiate exp and are in agreement with vt, and
 * the corresponding outcome values of evaluating exp on these tuples.
 *
 * since the function is recursive on the structure of exp,
 * its outputs must be stored at varying recursion depths.
 * we simply fix a max recursion depth, which should be highly uncritical.
 *
 * 
 * we implement the output sets by an array of dynamically growing
 * lists, where the array index is the recursion depth.
 *
 * the lists will be allocated new members every time their
 * current content exceeds their current number of elements.
 * lists are erased simply by setting their "current number"
 * counter to 0.
 */




/* #define RPG_MAXRECDEPTH 1000 */



/* /\* overall output */
/*  *\/ */
/* RPGvaluetuple_pointer lrecd_VT[RPG_MAXRECDEPTH];/\* pointers to start elements *\/ */
/* RPGvalue_pointer lrecd_V[RPG_MAXRECDEPTH]; */
/* int lnum_recd[RPG_MAXRECDEPTH]; */



/* /\* intermediate storage of lhs in +,-,*,/ */
/*  *\/ */
/* RPGvaluetuple_pointer lrecd_lhs_VT[RPG_MAXRECDEPTH]; */
/* RPGvalue_pointer lrecd_lhs_V[RPG_MAXRECDEPTH]; */
/* int lnum_recd_lhs[RPG_MAXRECDEPTH]; */







void RPG_get_VT_and_V(int recd, 
		      RPGlayer *t,
		      RPGvaluetuple *vt,
		      ExpNode *exp)

{

  static Bool *reshave;
  static float *resvt;
  static Bool fc = TRUE;

  RPGvaluetuple *ivt, *jvt, *kvt, *prevvt;
  RPGvalue *iv, *jv, *kv, *prevv;

  int i, j, k, l;
  float resv;



  /* these guys will serve to store the merged valuevector
   * before inserting it into the output data structure.
   */
  if ( fc ) {
    reshave = ( Bool * ) calloc(gnum_relevant_fluents, sizeof( Bool ));
    resvt = ( float * ) calloc(gnum_relevant_fluents, sizeof( float ));
    fc = FALSE;
  }



  if ( !exp ) {
    /* perhaps remove this warning later...
     */
    printf("\nwarning: empty expression.");
    lnum_recd[recd] = 0;
    return;
  }
  if ( recd >= RPG_MAXRECDEPTH ) {
    printf("\nexp recursion depth too high, %d. increase RPG_MAXRECDEPTH (RPGvaluetuples.c)\n\n", 
	   RPG_MAXRECDEPTH);
    exit( 1 );
  }
  if ( !lrecd_VT[recd] ) {
    lrecd_VT[recd] = new_RPGvaluetuple();
    lrecd_V[recd] = new_RPGvalue();
    lrecd_lhs_VT[recd] = new_RPGvaluetuple();
    lrecd_lhs_V[recd] = new_RPGvalue();
    /* these are unnecessary, but so what...
     */
    lnum_recd[recd] = 0;
    lnum_recd_lhs[recd] = 0;
  }



  /* do the different types of expressions.
   * LONG business.
   */
  switch ( exp->connective ) {



    /* FHEAD: a fluent
     */
  case FHEAD:
    if ( vt->have[exp->fl] ) {
      /* our input tuple has got something to say about this fluent.
       * just take this guy.
       *
       * res vt will care only about this guy, and have the respective value there.
       * res v will be the same value, naturally.
       */
      ivt = lrecd_VT[recd]->next;
      if ( !ivt ) {
	ivt = new_RPGvaluetuple();
	ivt->prev = lrecd_VT[recd];
	lrecd_VT[recd]->next = ivt;
      } else {
	/* EVERYWHERE, HERE AND BELOW, WE KEEP DON'T CARE
	 * VT VALUES TO -1 JUST FOR CONSISTENCY!!
	 * HAS NO REAL MEANING, COULD BE REMOVED.
	 */
	for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	  ivt->have[l] = FALSE;
	  ivt->vt[l] = -1;
	}
      }
      ivt->have[exp->fl] = TRUE;
      ivt->vt[exp->fl] = vt->vt[exp->fl];

      iv = lrecd_V[recd]->next;
      if ( !iv ) {
	iv = new_RPGvalue();
	iv->prev = lrecd_V[recd];
	lrecd_V[recd]->next = iv;
      }
      iv->v = vt->vt[exp->fl];

      lnum_recd[recd] = 1;

      break;
    }

    /* our input tuple has nothing to say about this fluent.
     * collect the values in the RPG layer t.
     */
    lnum_recd[recd] = 0;

    ivt = lrecd_VT[recd]->next;
    prevvt = lrecd_VT[recd];
    iv = lrecd_V[recd]->next;
    prevv = lrecd_V[recd];
    for ( jv = t->V[exp->fl]->next; jv; jv = jv->next ) {
      if ( !ivt ) {
	ivt = new_RPGvaluetuple();
	ivt->prev = prevvt;
	prevvt->next = ivt;
      } else {
	for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	  ivt->have[l] = FALSE;
	  ivt->vt[l] = -1;
	}
      }
      ivt->have[exp->fl] = TRUE;
      ivt->vt[exp->fl] = jv->v;

      if ( !iv ) {
	iv = new_RPGvalue();
	iv->prev = prevv;
	prevv->next = iv;
      }
      iv->v = jv->v;

      lnum_recd[recd]++;

      prevvt = ivt;
      ivt = ivt->next;
      prevv = iv;
      iv = iv->next;
    }   
    break;



    /* NUMBER: a number.
     */
  case NUMBER:
    /* just collect that number.
     * vt will be a complete "don't care"
     */
    ivt = lrecd_VT[recd]->next;
    if ( !ivt ) {
      ivt = new_RPGvaluetuple();
      ivt->prev = lrecd_VT[recd];
      lrecd_VT[recd]->next = ivt;
    } else {
      for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	ivt->have[l] = FALSE;
	ivt->vt[l] = -1;
      }
    }

    iv = lrecd_V[recd]->next;
    if ( !iv ) {
      iv = new_RPGvalue();
      iv->prev = lrecd_V[recd];
      lrecd_V[recd]->next = iv;
    }
    iv->v = exp->value;

    lnum_recd[recd] = 1;
    break;



    /* MINUS: inverted expression.
     */
  case MINUS:
    /* copy from below, and invert the values.
     */

    /* first do the expression below.
     */
    RPG_get_VT_and_V(recd+1, t, vt, exp->son);

    /* now invert values and insert into recd.
     */
    ivt = lrecd_VT[recd]->next;
    prevvt = lrecd_VT[recd];
    jvt = lrecd_VT[recd+1]->next;
    iv = lrecd_V[recd]->next;
    prevv = lrecd_V[recd];
    jv = lrecd_V[recd+1]->next;
    for ( j = 0; j < lnum_recd[recd+1]; j++ ) {
      if ( !jvt || !jv ) {
	printf("\nleaving allocated jvt/jv space at recd+1?\n\n");
	exit( 1 );
      }

      if ( !ivt ) {
	ivt = new_RPGvaluetuple();
	ivt->prev = prevvt;
	prevvt->next = ivt;
      }
      for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	ivt->have[l] = jvt->have[l];
	/* remember: the values of the *vars* are the same!!
	 */
	ivt->vt[l] = jvt->vt[l];
      }

      if ( !iv ) {
	iv = new_RPGvalue();
	iv->prev = prevv;
	prevv->next = iv;
      }
      iv->v = (-1) * jv->v;

      prevvt = ivt;
      ivt = ivt->next;
      prevv = iv;
      iv = iv->next;

      jvt = jvt->next;
      jv = jv->next;
    }

    lnum_recd[recd] = lnum_recd[recd+1];
    break;



    /* AD: add two expressions.
     */
  case AD:
    /* collect the lhs stuff into recd+1, and store in lhs storage at recd.
     * then collect the rhs stuff into recd+1.
     * then merge this stuff: take all pairs of vectors that are not in
     * contradiction, and put the merged vectors and added values into
     * storage at recd.
     */

    /* collect the lhs stuff into recd+1.
     */
    RPG_get_VT_and_V(recd+1, t, vt, exp->leftson);

    /* copy this into lrecd_lhs .. [recd].
     */
    ivt = lrecd_lhs_VT[recd]->next;
    prevvt = lrecd_lhs_VT[recd];
    jvt = lrecd_VT[recd+1]->next;
    iv = lrecd_lhs_V[recd]->next;
    prevv = lrecd_lhs_V[recd];
    jv = lrecd_V[recd+1]->next;
    for ( j = 0; j < lnum_recd[recd+1]; j++ ) {
      if ( !jvt || !jv ) {
	printf("\nleaving allocated jvt/jv space at recd+1?\n\n");
	exit( 1 );
      }

      if ( !ivt ) {
	ivt = new_RPGvaluetuple();
	ivt->prev = prevvt;
	prevvt->next = ivt;
      }
      for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	ivt->have[l] = jvt->have[l];
	ivt->vt[l] = jvt->vt[l];
      }

      if ( !iv ) {
	iv = new_RPGvalue();
	iv->prev = prevv;
	prevv->next = iv;
      }
      iv->v = jv->v;

      prevvt = ivt;
      ivt = ivt->next;
      prevv = iv;
      iv = iv->next;

      jvt = jvt->next;
      jv = jv->next;
    }
    lnum_recd_lhs[recd] = lnum_recd[recd+1];

    /* now, collect the rhs stuff into recd+1.
     */
    RPG_get_VT_and_V(recd+1, t, vt, exp->rightson);

    /* compute all pairs, filter out contradictory ones,
     * and store the others in recd_VT[recd], recd_V[recd].
     */
    lnum_recd[recd] = 0;
    ivt = lrecd_lhs_VT[recd]->next;
    iv = lrecd_lhs_V[recd]->next;
    for ( i = 0; i < lnum_recd_lhs[recd]; i++ ) {
      if ( !ivt || !iv ) {
	printf("\nleaving allocated ivt/iv space at merge, lhs recd?\n\n");
	exit( 1 );
      }

      jvt = lrecd_VT[recd+1]->next;
      jv = lrecd_V[recd+1]->next;
      for ( j = 0; j < lnum_recd[recd+1]; j++ ) {
	if ( !jvt || !jv ) {
	  printf("\nleaving allocated jvt/jv space at merge, recd+1?\n\n");
	  exit( 1 );
	}

	/* check if there's a contradiction. simple.
	 * assemble merged vector at the same time.
	 */
	for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	  if ( ivt->have[l] && jvt->have[l] && ivt->vt[l] != jvt->vt[l] ) {
	    break;
	  }
	  if ( ivt->have[l] ) {
	    reshave[l] = TRUE;
	    resvt[l] = ivt->vt[l];
	    continue;
	  }
	  if ( jvt->have[l] ) {
	    reshave[l] = TRUE;
	    resvt[l] = jvt->vt[l];
	    continue;
	  }
	  reshave[l] = FALSE;
	  resvt[l] = -1;
	}
	if ( l < gnum_relevant_fluents ) {
	  /* there's a fluent on which these guys disagree. skip!
	   */
	  jvt = jvt->next;
	  jv = jv->next;
	  continue;
	}

	/* lhs + rhs
	 */
	resv = iv->v + jv->v;

	/* go through lrecd_VT[recd] and lrecd_V[recd], checking for duplicates
	 * just for the sake of debugging; list end is found at the same time.
	 * if no bug, insert at end.
	 *
	 * INEFFICIENT! once "finished debugging", maybe use a current list end 
	 * pointer here.
	 */
	kvt = lrecd_VT[recd]->next;
	prevvt = lrecd_VT[recd];
	kv = lrecd_V[recd]->next;
	prevv = lrecd_V[recd];
	for ( k = 0; k < lnum_recd[recd]; k++ ) {
	  if ( !kvt || !kv ) {
	    printf("\nleaving allocated kvt/kv space at merge, recd?\n\n");
	    exit( 1 );
	  }
	  /* check if value tuples are the same.
	   */
	  for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	    if ( reshave[l] != kvt->have[l] ||
		 resvt[l] != kvt->vt[l] ) {
	      break;
	    }
	  }
	  if ( l == gnum_relevant_fluents ) {
	    if ( resv != kv->v ) {
	      printf("\nsame tuples, different values in add?? this is definitely a bug.\n\n");
	      exit( 1 );
	    }
	    printf("\nsame tuples in add?? i think this is a bug.\n\n");
	    exit( 1 );
	  }
	  prevvt = kvt;
	  kvt = kvt->next;
	  prevv = kv;
	  kv = kv->next;
	}

	/* insert at end ie as prevv(t)->next = kv(t).
	 */
	if ( !kvt ) {
	  kvt = new_RPGvaluetuple();
	  kvt->prev = prevvt;
	  prevvt->next = kvt;
	}
	for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	  kvt->have[l] = reshave[l];
	  kvt->vt[l] = resvt[l];
	}

	if ( !kv ) {
	  kv = new_RPGvalue();
	  kv->prev = prevv;
	  prevv->next = kv;
	}
	kv->v = resv;

	lnum_recd[recd]++;

	jvt = jvt->next;
	jv = jv->next;
      } /* endfor j, jv, jvt over rhs outcome in recd+1 */
      ivt = ivt->next;
      iv = iv->next;
    } /* endfor i, iv, ivt over lhs outcome in lhs recd */
    break;



    /* SU: subtract two expressions.
     */
  case SU:
    /* collect the lhs stuff into recd+1, and store in lhs storage at recd.
     * then collect the rhs stuff into recd+1.
     * then merge this stuff: take all pairs of vectors that are not in
     * contradiction, and put the merged vectors and subtracted values into
     * storage at recd.
     */

    /* collect the lhs stuff into recd+1.
     */
    RPG_get_VT_and_V(recd+1, t, vt, exp->leftson);

    /* copy this into lrecd_lhs .. [recd].
     */
    ivt = lrecd_lhs_VT[recd]->next;
    prevvt = lrecd_lhs_VT[recd];
    jvt = lrecd_VT[recd+1]->next;
    iv = lrecd_lhs_V[recd]->next;
    prevv = lrecd_lhs_V[recd];
    jv = lrecd_V[recd+1]->next;
    for ( j = 0; j < lnum_recd[recd+1]; j++ ) {
      if ( !jvt || !jv ) {
	printf("\nleaving allocated jvt/jv space at recd+1?\n\n");
	exit( 1 );
      }

      if ( !ivt ) {
	ivt = new_RPGvaluetuple();
	ivt->prev = prevvt;
	prevvt->next = ivt;
      }
      for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	ivt->have[l] = jvt->have[l];
	ivt->vt[l] = jvt->vt[l];
      }

      if ( !iv ) {
	iv = new_RPGvalue();
	iv->prev = prevv;
	prevv->next = iv;
      }
      iv->v = jv->v;

      prevvt = ivt;
      ivt = ivt->next;
      prevv = iv;
      iv = iv->next;

      jvt = jvt->next;
      jv = jv->next;
    }
    lnum_recd_lhs[recd] = lnum_recd[recd+1];

    /* now, collect the rhs stuff into recd+1.
     */
    RPG_get_VT_and_V(recd+1, t, vt, exp->rightson);

    /* compute all pairs, filter out contradictory ones,
     * and store the others in recd_VT[recd], recd_V[recd].
     */
    lnum_recd[recd] = 0;
    ivt = lrecd_lhs_VT[recd]->next;
    iv = lrecd_lhs_V[recd]->next;
    for ( i = 0; i < lnum_recd_lhs[recd]; i++ ) {
      if ( !ivt || !iv ) {
	printf("\nleaving allocated ivt/iv space at merge, lhs recd?\n\n");
	exit( 1 );
      }

      jvt = lrecd_VT[recd+1]->next;
      jv = lrecd_V[recd+1]->next;
      for ( j = 0; j < lnum_recd[recd+1]; j++ ) {
	if ( !jvt || !jv ) {
	  printf("\nleaving allocated jvt/jv space at merge, recd+1?\n\n");
	  exit( 1 );
	}

	/* check if there's a contradiction. simple.
	 * assemble merged vector at the same time.
	 */
	for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	  if ( ivt->have[l] && jvt->have[l] && ivt->vt[l] != jvt->vt[l] ) {
	    break;
	  }
	  if ( ivt->have[l] ) {
	    reshave[l] = TRUE;
	    resvt[l] = ivt->vt[l];
	    continue;
	  }
	  if ( jvt->have[l] ) {
	    reshave[l] = TRUE;
	    resvt[l] = jvt->vt[l];
	    continue;
	  }
	  reshave[l] = FALSE;
	  resvt[l] = -1;
	}
	if ( l < gnum_relevant_fluents ) {
	  /* there's a fluent on which these guys disagree. skip!
	   */
	  jvt = jvt->next;
	  jv = jv->next;
	  continue;
	}

	/* lhs - rhs
	 */
	resv = iv->v - jv->v;

	/* go through lrecd_VT[recd] and lrecd_V[recd], checking for duplicates
	 * just for the sake of debugging; list end is found at the same time.
	 * if no bug, insert at end.
	 *
	 * INEFFICIENT! once "finished debugging", maybe use a current list end 
	 * pointer here.
	 */
	kvt = lrecd_VT[recd]->next;
	prevvt = lrecd_VT[recd];
	kv = lrecd_V[recd]->next;
	prevv = lrecd_V[recd];
	for ( k = 0; k < lnum_recd[recd]; k++ ) {
	  if ( !kvt || !kv ) {
	    printf("\nleaving allocated kvt/kv space at merge, recd?\n\n");
	    exit( 1 );
	  }
	  /* check if value tuples are the same.
	   */
	  for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	    if ( reshave[l] != kvt->have[l] ||
		 resvt[l] != kvt->vt[l] ) {
	      break;
	    }
	  }
	  if ( l == gnum_relevant_fluents ) {
	    if ( resv != kv->v ) {
	      printf("\nsame tuples, different values in sub?? this is definitely a bug.\n\n");
	      exit( 1 );
	    }
	    printf("\nsame tuples in sub?? i think this is a bug.\n\n");
	    exit( 1 );
	  }
	  prevvt = kvt;
	  kvt = kvt->next;
	  prevv = kv;
	  kv = kv->next;
	}

	/* insert at end ie as prevv(t)->next = kv(t).
	 */
	if ( !kvt ) {
	  kvt = new_RPGvaluetuple();
	  kvt->prev = prevvt;
	  prevvt->next = kvt;
	}
	for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	  kvt->have[l] = reshave[l];
	  kvt->vt[l] = resvt[l];
	}

	if ( !kv ) {
	  kv = new_RPGvalue();
	  kv->prev = prevv;
	  prevv->next = kv;
	}
	kv->v = resv;

	lnum_recd[recd]++;

	jvt = jvt->next;
	jv = jv->next;
      } /* endfor j, jv, jvt over rhs outcome in recd+1 */
      ivt = ivt->next;
      iv = iv->next;
    } /* endfor i, iv, ivt over lhs outcome in lhs recd */
    break;



    /* MU: multiply two expressions.
     */
  case MU:
    /* collect the lhs stuff into recd+1, and store in lhs storage at recd.
     * then collect the rhs stuff into recd+1.
     * then merge this stuff: take all pairs of vectors that are not in
     * contradiction, and put the merged vectors and value product into
     * storage at recd.
     */

    /* collect the lhs stuff into recd+1.
     */
    RPG_get_VT_and_V(recd+1, t, vt, exp->leftson);

    /* copy this into lrecd_lhs .. [recd].
     */
    ivt = lrecd_lhs_VT[recd]->next;
    prevvt = lrecd_lhs_VT[recd];
    jvt = lrecd_VT[recd+1]->next;
    iv = lrecd_lhs_V[recd]->next;
    prevv = lrecd_lhs_V[recd];
    jv = lrecd_V[recd+1]->next;
    for ( j = 0; j < lnum_recd[recd+1]; j++ ) {
      if ( !jvt || !jv ) {
	printf("\nleaving allocated jvt/jv space at recd+1?\n\n");
	exit( 1 );
      }

      if ( !ivt ) {
	ivt = new_RPGvaluetuple();
	ivt->prev = prevvt;
	prevvt->next = ivt;
      }
      for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	ivt->have[l] = jvt->have[l];
	ivt->vt[l] = jvt->vt[l];
      }

      if ( !iv ) {
	iv = new_RPGvalue();
	iv->prev = prevv;
	prevv->next = iv;
      }
      iv->v = jv->v;

      prevvt = ivt;
      ivt = ivt->next;
      prevv = iv;
      iv = iv->next;

      jvt = jvt->next;
      jv = jv->next;
    }
    lnum_recd_lhs[recd] = lnum_recd[recd+1];

    /* now, collect the rhs stuff into recd+1.
     */
    RPG_get_VT_and_V(recd+1, t, vt, exp->rightson);

    /* compute all pairs, filter out contradictory ones,
     * and store the others in recd_VT[recd], recd_V[recd].
     */
    lnum_recd[recd] = 0;
    ivt = lrecd_lhs_VT[recd]->next;
    iv = lrecd_lhs_V[recd]->next;
    for ( i = 0; i < lnum_recd_lhs[recd]; i++ ) {
      if ( !ivt || !iv ) {
	printf("\nleaving allocated ivt/iv space at merge, lhs recd?\n\n");
	exit( 1 );
      }

      jvt = lrecd_VT[recd+1]->next;
      jv = lrecd_V[recd+1]->next;
      for ( j = 0; j < lnum_recd[recd+1]; j++ ) {
	if ( !jvt || !jv ) {
	  printf("\nleaving allocated jvt/jv space at merge, recd+1?\n\n");
	  exit( 1 );
	}

	/* check if there's a contradiction. simple.
	 * assemble merged vector at the same time.
	 */
	for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	  if ( ivt->have[l] && jvt->have[l] && ivt->vt[l] != jvt->vt[l] ) {
	    break;
	  }
	  if ( ivt->have[l] ) {
	    reshave[l] = TRUE;
	    resvt[l] = ivt->vt[l];
	    continue;
	  }
	  if ( jvt->have[l] ) {
	    reshave[l] = TRUE;
	    resvt[l] = jvt->vt[l];
	    continue;
	  }
	  reshave[l] = FALSE;
	  resvt[l] = -1;
	}
	if ( l < gnum_relevant_fluents ) {
	  /* there's a fluent on which these guys disagree. skip!
	   */
	  jvt = jvt->next;
	  jv = jv->next;
	  continue;
	}

	/* lhs * rhs
	 */
	resv = iv->v * jv->v;

	/* go through lrecd_VT[recd] and lrecd_V[recd], checking for duplicates
	 * just for the sake of debugging; list end is found at the same time.
	 * if no bug, insert at end.
	 *
	 * INEFFICIENT! once "finished debugging", maybe use a current list end 
	 * pointer here.
	 */
	kvt = lrecd_VT[recd]->next;
	prevvt = lrecd_VT[recd];
	kv = lrecd_V[recd]->next;
	prevv = lrecd_V[recd];
	for ( k = 0; k < lnum_recd[recd]; k++ ) {
	  if ( !kvt || !kv ) {
	    printf("\nleaving allocated kvt/kv space at merge, recd?\n\n");
	    exit( 1 );
	  }
	  /* check if value tuples are the same.
	   */
	  for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	    if ( reshave[l] != kvt->have[l] ||
		 resvt[l] != kvt->vt[l] ) {
	      break;
	    }
	  }
	  if ( l == gnum_relevant_fluents ) {
	    if ( resv != kv->v ) {
	      printf("\nsame tuples, different values in mul?? this is definitely a bug.\n\n");
	      exit( 1 );
	    }
	    printf("\nsame tuples in mul?? i think this is a bug.\n\n");
	    exit( 1 );
	  }
	  prevvt = kvt;
	  kvt = kvt->next;
	  prevv = kv;
	  kv = kv->next;
	}

	/* insert at end ie as prevv(t)->next = kv(t).
	 */
	if ( !kvt ) {
	  kvt = new_RPGvaluetuple();
	  kvt->prev = prevvt;
	  prevvt->next = kvt;
	}
	for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	  kvt->have[l] = reshave[l];
	  kvt->vt[l] = resvt[l];
	}

	if ( !kv ) {
	  kv = new_RPGvalue();
	  kv->prev = prevv;
	  prevv->next = kv;
	}
	kv->v = resv;

	lnum_recd[recd]++;

	jvt = jvt->next;
	jv = jv->next;
      } /* endfor j, jv, jvt over rhs outcome in recd+1 */
      ivt = ivt->next;
      iv = iv->next;
    } /* endfor i, iv, ivt over lhs outcome in lhs recd */
    break;



    /* DI: divide two expressions.
     */
  case DI:
    /* collect the lhs stuff into recd+1, and store in lhs storage at recd.
     * then collect the rhs stuff into recd+1.
     * then merge this stuff: take all pairs of vectors that are not in
     * contradiction, and put the merged vectors and value quotient into
     * storage at recd.
     */

    /* collect the lhs stuff into recd+1.
     */
    RPG_get_VT_and_V(recd+1, t, vt, exp->leftson);

    /* copy this into lrecd_lhs .. [recd].
     */
    ivt = lrecd_lhs_VT[recd]->next;
    prevvt = lrecd_lhs_VT[recd];
    jvt = lrecd_VT[recd+1]->next;
    iv = lrecd_lhs_V[recd]->next;
    prevv = lrecd_lhs_V[recd];
    jv = lrecd_V[recd+1]->next;
    for ( j = 0; j < lnum_recd[recd+1]; j++ ) {
      if ( !jvt || !jv ) {
	printf("\nleaving allocated jvt/jv space at recd+1?\n\n");
	exit( 1 );
      }

      if ( !ivt ) {
	ivt = new_RPGvaluetuple();
	ivt->prev = prevvt;
	prevvt->next = ivt;
      }
      for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	ivt->have[l] = jvt->have[l];
	ivt->vt[l] = jvt->vt[l];
      }

      if ( !iv ) {
	iv = new_RPGvalue();
	iv->prev = prevv;
	prevv->next = iv;
      }
      iv->v = jv->v;

      prevvt = ivt;
      ivt = ivt->next;
      prevv = iv;
      iv = iv->next;

      jvt = jvt->next;
      jv = jv->next;
    }
    lnum_recd_lhs[recd] = lnum_recd[recd+1];

    /* now, collect the rhs stuff into recd+1.
     */
    RPG_get_VT_and_V(recd+1, t, vt, exp->rightson);

    /* compute all pairs, filter out contradictory ones,
     * and store the others in recd_VT[recd], recd_V[recd].
     */
    lnum_recd[recd] = 0;
    ivt = lrecd_lhs_VT[recd]->next;
    iv = lrecd_lhs_V[recd]->next;
    for ( i = 0; i < lnum_recd_lhs[recd]; i++ ) {
      if ( !ivt || !iv ) {
	printf("\nleaving allocated ivt/iv space at merge, lhs recd?\n\n");
	exit( 1 );
      }

      jvt = lrecd_VT[recd+1]->next;
      jv = lrecd_V[recd+1]->next;
      for ( j = 0; j < lnum_recd[recd+1]; j++ ) {
	if ( !jvt || !jv ) {
	  printf("\nleaving allocated jvt/jv space at merge, recd+1?\n\n");
	  exit( 1 );
	}

	/* check if there's a contradiction. simple.
	 * assemble merged vector at the same time.
	 */
	for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	  if ( ivt->have[l] && jvt->have[l] && ivt->vt[l] != jvt->vt[l] ) {
	    break;
	  }
	  if ( ivt->have[l] ) {
	    reshave[l] = TRUE;
	    resvt[l] = ivt->vt[l];
	    continue;
	  }
	  if ( jvt->have[l] ) {
	    reshave[l] = TRUE;
	    resvt[l] = jvt->vt[l];
	    continue;
	  }
	  reshave[l] = FALSE;
	  resvt[l] = -1;
	}
	if ( l < gnum_relevant_fluents ) {
	  /* there's a fluent on which these guys disagree. skip!
	   */
	  jvt = jvt->next;
	  jv = jv->next;
	  continue;
	}

	/* lhs / rhs
	 */
	if ( jv->v == 0 ) {
	  /* quotient undefined. simply skip this pair.
	   */
	  jvt = jvt->next;
	  jv = jv->next;
	  continue;
	}
	resv = iv->v / jv->v;

	/* go through lrecd_VT[recd] and lrecd_V[recd], checking for duplicates
	 * just for the sake of debugging; list end is found at the same time.
	 * if no bug, insert at end.
	 *
	 * INEFFICIENT! once "finished debugging", maybe use a current list end 
	 * pointer here.
	 */
	kvt = lrecd_VT[recd]->next;
	prevvt = lrecd_VT[recd];
	kv = lrecd_V[recd]->next;
	prevv = lrecd_V[recd];
	for ( k = 0; k < lnum_recd[recd]; k++ ) {
	  if ( !kvt || !kv ) {
	    printf("\nleaving allocated kvt/kv space at merge, recd?\n\n");
	    exit( 1 );
	  }
	  /* check if value tuples are the same.
	   */
	  for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	    if ( reshave[l] != kvt->have[l] ||
		 resvt[l] != kvt->vt[l] ) {
	      break;
	    }
	  }
	  if ( l == gnum_relevant_fluents ) {
	    if ( resv != kv->v ) {
	      printf("\nsame tuples, different values in div?? this is definitely a bug.\n\n");
	      exit( 1 );
	    }
	    printf("\nsame tuples in div?? i think this is a bug.\n\n");
	    exit( 1 );
	  }
	  prevvt = kvt;
	  kvt = kvt->next;
	  prevv = kv;
	  kv = kv->next;
	}

	/* insert at end ie as prevv(t)->next = kv(t).
	 */
	if ( !kvt ) {
	  kvt = new_RPGvaluetuple();
	  kvt->prev = prevvt;
	  prevvt->next = kvt;
	}
	for ( l = 0; l < gnum_relevant_fluents; l++ ) {
	  kvt->have[l] = reshave[l];
	  kvt->vt[l] = resvt[l];
	}

	if ( !kv ) {
	  kv = new_RPGvalue();
	  kv->prev = prevv;
	  prevv->next = kv;
	}
	kv->v = resv;

	lnum_recd[recd]++;

	jvt = jvt->next;
	jv = jv->next;
      } /* endfor j, jv, jvt over rhs outcome in recd+1 */
      ivt = ivt->next;
      iv = iv->next;
    } /* endfor i, iv, ivt over lhs outcome in lhs recd */
    break;
  default:
    printf("\nunknown exp connective.\n\n");
    exit( 1 );
  }

}






