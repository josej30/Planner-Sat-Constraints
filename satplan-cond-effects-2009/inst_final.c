


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
 * File: inst_final.c
 * Description: final domain representation functions
 *
 *
 * Author: Joerg Hoffmann 2000
 *
 *********************************************************************/ 









#include "num2sat.h"

#include "output.h"
#include "memory.h"

#include "inst_pre.h"
#include "inst_final.h"














/********************************
 * POSSIBLY TRUE FACTS ANALYSIS *
 ********************************/








/* local globals for this part
 */

int_pointer lpos[MAX_PREDICATES];
int_pointer lneg[MAX_PREDICATES];
int_pointer luse[MAX_PREDICATES];
int_pointer lindex[MAX_PREDICATES];

int lp;
int largs[MAX_VARS];



/* for collecting poss. defined fluents
 */
int_pointer lf_def[MAX_FUNCTIONS];
int_pointer lf_index[MAX_FUNCTIONS];

int lf;
int lf_args[MAX_VARS];






void perform_reachability_analysis( void )

{

  int size, i, j, k, adr, num;
  Bool fixpoint;
  Facts *f;
  NormOperator *no;
  EasyTemplate *t1, *t2;
  NormEffect *ne;
  Action *tmp, *a;
  Bool *had_hard_template;
  PseudoAction *pa;
  PseudoActionEffect *pae;

  gactions = NULL;
  gnum_actions = 0;

  for ( i = 0; i < gnum_predicates; i++ ) {
    size =  1;
    for ( j = 0; j < garity[i]; j++ ) {
      size *= gnum_constants;
    }

    lpos[i] = ( int_pointer ) calloc( size, sizeof( int ) );
    lneg[i] = ( int_pointer ) calloc( size, sizeof( int ) );
    luse[i] = ( int_pointer ) calloc( size, sizeof( int ) );
    lindex[i] = ( int_pointer ) calloc( size, sizeof( int ) );

    for ( j = 0; j < size; j++ ) {
      lpos[i][j] = 0;
      lneg[i][j] = 1;/* all facts but initials are poss. negative */
      luse[i][j] = 0;
      lindex[i][j] = -1;
    }
  }

  had_hard_template = ( Bool * ) calloc( gnum_hard_templates, sizeof( Bool ) );
  for ( i = 0; i < gnum_hard_templates; i++ ) {
    had_hard_template[i] = FALSE;
  }

  /* mark initial facts as possibly positive, not poss. negative
   */
  for ( i = 0; i < gnum_predicates; i++ ) {
    lp = i;
    for ( j = 0; j < gnum_initial_predicate[i]; j++ ) {
      for ( k = 0; k < garity[i]; k++ ) {
	largs[k] = ginitial_predicate[i][j].args[k];
      }
      adr = fact_adress();
      lpos[lp][adr] = 1;
      lneg[lp][adr] = 0;
    }
  }

  /* compute fixpoint
   */
  fixpoint = FALSE;
  while ( !fixpoint ) {
    fixpoint = TRUE;

    /* assign next layer of easy templates to possibly positive fixpoint
     */
    t1 = geasy_templates;
    while ( t1 ) {
      no = t1->op;
      for ( i = 0; i < no->num_preconds; i++ ) {
	lp = no->preconds[i].predicate;
	for ( j = 0; j < garity[lp]; j++ ) {
	  largs[j] = ( no->preconds[i].args[j] >= 0 ) ?
	    no->preconds[i].args[j] : t1->inst_table[DECODE_VAR( no->preconds[i].args[j] )];
	}
	if ( !lpos[lp][fact_adress()] ) {
	  break;
	}
      }

      if ( i < no->num_preconds ) {
	t1 = t1->next;
	continue;
      }

      num = 0;
      for ( ne = no->effects; ne; ne = ne->next ) {
	num++;
	/* currently, simply ignore effect conditions and assume
	 * they will all be made true eventually.
	 */
	for ( i = 0; i < ne->num_adds; i++ ) {
	  lp = ne->adds[i].predicate;
	  for ( j = 0; j < garity[lp]; j++ ) {
	    largs[j] = ( ne->adds[i].args[j] >= 0 ) ?
	      ne->adds[i].args[j] : t1->inst_table[DECODE_VAR( ne->adds[i].args[j] )];
	  }
	  adr = fact_adress();
	  if ( !lpos[lp][adr] ) {
	    /* new relevant fact! (added non initial)
	     */
	    lpos[lp][adr] = 1;
	    lneg[lp][adr] = 1;
	    luse[lp][adr] = 1;
	    if ( gnum_relevant_facts == MAX_RELEVANT_FACTS ) {
	      printf("\ntoo many relevant facts! increase MAX_RELEVANT_FACTS (currently %d)\n\n",
		     MAX_RELEVANT_FACTS);
	      exit( 1 );
	    }
	    grelevant_facts[gnum_relevant_facts].predicate = lp;
	    for ( j = 0; j < garity[lp]; j++ ) {
	      grelevant_facts[gnum_relevant_facts].args[j] = largs[j];
	    }
	    lindex[lp][adr] = gnum_relevant_facts;
	    gnum_relevant_facts++;
	    fixpoint = FALSE;
	  }
	}
      }

      tmp = new_Action();
      tmp->norm_operator = no;
      for ( i = 0; i < no->num_vars; i++ ) {
	tmp->inst_table[i] = t1->inst_table[i];
      }
      tmp->name = no->operator->name;
      tmp->num_name_vars = no->operator->number_of_real_params;
      make_name_inst_table_from_NormOperator( tmp, no, t1 );
      tmp->next = gactions;
      tmp->num_effects = num;
      gactions = tmp;
      gnum_actions++;

      t2 = t1->next;
      if ( t1->next ) {
	t1->next->prev = t1->prev;
      }
      if ( t1->prev ) {
	t1->prev->next = t1->next;
      } else {
	geasy_templates = t1->next;
      }
      free_single_EasyTemplate( t1 );
      t1 = t2;
    }

    /* now assign all hard templates that have not been transformed
     * to actions yet.
     */
    for ( i = 0; i < gnum_hard_templates; i++ ) {
      if ( had_hard_template[i] ) {
	continue;
      }
      pa = ghard_templates[i];

      for ( j = 0; j < pa->num_preconds; j++ ) {
	lp = pa->preconds[j].predicate;
	for ( k = 0; k < garity[lp]; k++ ) {
	  largs[k] = pa->preconds[j].args[k];
	}
	if ( !lpos[lp][fact_adress()] ) {
	  break;
	}
      }

      if ( j < pa->num_preconds ) {
	continue;
      }

      for ( pae = pa->effects; pae; pae = pae->next ) {
	/* currently, simply ignore effect conditions and assume
	 * they will all be made true eventually.
	 */
	for ( j = 0; j < pae->num_adds; j++ ) {
	  lp = pae->adds[j].predicate;
	  for ( k = 0; k < garity[lp]; k++ ) {
	    largs[k] = pae->adds[j].args[k];
	  }
	  adr = fact_adress();
	  if ( !lpos[lp][adr] ) {
	    /* new relevant fact! (added non initial)
	     */
	    lpos[lp][adr] = 1;
	    lneg[lp][adr] = 1;
	    luse[lp][adr] = 1;
	    if ( gnum_relevant_facts == MAX_RELEVANT_FACTS ) {
	      printf("\ntoo many relevant facts! increase MAX_RELEVANT_FACTS (currently %d)\n\n",
		     MAX_RELEVANT_FACTS);
	      exit( 1 );
	    }
	    grelevant_facts[gnum_relevant_facts].predicate = lp;
	    for ( k = 0; k < garity[lp]; k++ ) {
	      grelevant_facts[gnum_relevant_facts].args[k] = largs[k];
	    }
	    lindex[lp][adr] = gnum_relevant_facts;
	    gnum_relevant_facts++;
	    fixpoint = FALSE;
	  }
	}
      }

      tmp = new_Action();
      tmp->pseudo_action = pa;
      for ( j = 0; j < pa->operator->num_vars; j++ ) {
	tmp->inst_table[j] = pa->inst_table[j];
      }
      tmp->name = pa->operator->name;
      tmp->num_name_vars = pa->operator->number_of_real_params;
      make_name_inst_table_from_PseudoAction( tmp, pa );
      tmp->next = gactions;
      tmp->num_effects = pa->num_effects;
      gactions = tmp;
      gnum_actions++;

      had_hard_template[i] = TRUE;
    }
  }

  free( had_hard_template );

  gnum_pp_facts = gnum_initial + gnum_relevant_facts;

  if ( gcmd_line.display_info == 118 ) {
    printf("\nreachability analysys came up with:");

    printf("\n\npossibly positive facts:");
    for ( f = ginitial; f; f = f->next ) {
      printf("\n");
      print_Fact( f->fact );
    }
    for ( i = 0; i < gnum_relevant_facts; i++ ) {
      printf("\n");
      print_Fact( &(grelevant_facts[i]) );
    }

    printf("\n\nthis yields these %d action templates:", gnum_actions);
    for ( i = 0; i < gnum_operators; i++ ) {
      printf("\n\noperator %s:", goperators[i]->name);
      for ( a = gactions; a; a = a->next ) {
	if ( ( a->norm_operator && 
	       a->norm_operator->operator !=  goperators[i] ) ||
	     ( a->pseudo_action &&
	       a->pseudo_action->operator !=  goperators[i] ) ) {
	  continue;
	}
	printf("\ntemplate: ");
	for ( j = 0; j < goperators[i]->number_of_real_params; j++ ) {
	  printf("%s", gconstants[a->name_inst_table[j]]);
	  if ( j < goperators[i]->num_vars-1 ) {
	    printf(" ");
	  }
	}
      }
    }
    printf("\n\n");
  }

}



int fact_adress( void )

{

  int r = 0, b = 1, i;

  for ( i = garity[lp] - 1; i > -1; i-- ) {
    r += b * largs[i];
    b *= gnum_constants;
  }

  return r;

}



int fluent_adress( void )

{

  int r = 0, b = 1, i;

  for ( i = gf_arity[lf] - 1; i > -1; i-- ) {
    r += b * lf_args[i];
    b *= gnum_constants;
  }

  return r;

}



void make_name_inst_table_from_NormOperator( Action *a, NormOperator *o, EasyTemplate *t )

{

  int i, r = 0, m = 0;

  for ( i = 0; i < o->operator->number_of_real_params; i++ ) {
    if ( o->num_removed_vars > r &&
	 o->removed_vars[r] == i ) {
      /* this var has been removed in NormOp;
       * insert type constraint constant
       *
       * at least one there, as empty typed pars ops are removed
       */
      a->name_inst_table[i] = gtype_consts[o->type_removed_vars[r]][0];
      r++;
    } else {
      /* this par corresponds to par m  in NormOp
       */
      a->name_inst_table[i] = t->inst_table[m];
      m++;
    }
  }

}



void make_name_inst_table_from_PseudoAction( Action *a, PseudoAction *pa )

{

  int i;

  for ( i = 0; i < pa->operator->number_of_real_params; i++ ) {
    a->name_inst_table[i] = pa->inst_table[i];
  }

}


















/***********************************************************
 * RELEVANCE ANALYSIS AND FINAL DOMAIN AND PROBLEM CLEANUP *
 ***********************************************************/









/* counts effects for later allocation
 */
int lnum_effects;









void collect_relevant_facts_and_fluents( void )

{

  Action *a;
  NormOperator *no;
  NormEffect *ne;
  int i, j, adr, size;
  PseudoAction *pa;
  PseudoActionEffect *pae;
  FluentValues *fvs;

  /* facts: mark all deleted facts; such facts, that are also pos, are relevant.
   */
  for ( a = gactions; a; a = a->next ) {
    if ( a->norm_operator ) {
      no = a->norm_operator;

      for ( ne = no->effects; ne; ne = ne->next ) {
	for ( i = 0; i < ne->num_dels; i++ ) {
	  lp = ne->dels[i].predicate;
	  for ( j = 0; j < garity[lp]; j++ ) {
	    largs[j] = ( ne->dels[i].args[j] >= 0 ) ?
	      ne->dels[i].args[j] : a->inst_table[DECODE_VAR( ne->dels[i].args[j] )];
	  }
	  adr = fact_adress();

	  lneg[lp][adr] = 1;
	  if ( lpos[lp][adr] &&
	       !luse[lp][adr] ) {
	    luse[lp][adr] = 1;
	    lindex[lp][adr] = gnum_relevant_facts;
	    if ( gnum_relevant_facts == MAX_RELEVANT_FACTS ) {
	      printf("\nincrease MAX_RELEVANT_FACTS! (current value: %d)\n\n",
		     MAX_RELEVANT_FACTS);
	      exit( 1 );
	    }
	    grelevant_facts[gnum_relevant_facts].predicate = lp;
	    for ( j = 0; j < garity[lp]; j++ ) {
	      grelevant_facts[gnum_relevant_facts].args[j] = largs[j];
	    }
	    lindex[lp][adr] = gnum_relevant_facts;
	    gnum_relevant_facts++;
	  }
	}
      }
    } else {
      pa = a->pseudo_action;

      for ( pae = pa->effects; pae; pae = pae->next ) {
	for ( i = 0; i < pae->num_dels; i++ ) {
	  lp = pae->dels[i].predicate;
	  for ( j = 0; j < garity[lp]; j++ ) {
	    largs[j] = pae->dels[i].args[j];
	  }
	  adr = fact_adress();

	  lneg[lp][adr] = 1;
	  if ( lpos[lp][adr] &&
	       !luse[lp][adr] ) {
	    luse[lp][adr] = 1;
	    lindex[lp][adr] = gnum_relevant_facts;
	    if ( gnum_relevant_facts == MAX_RELEVANT_FACTS ) {
	      printf("\nincrease MAX_RELEVANT_FACTS! (current value: %d)\n\n",
		     MAX_RELEVANT_FACTS);
	      exit( 1 );
	    }
	    grelevant_facts[gnum_relevant_facts].predicate = lp;
	    for ( j = 0; j < garity[lp]; j++ ) {
	      grelevant_facts[gnum_relevant_facts].args[j] = largs[j];
	    }
	    lindex[lp][adr] = gnum_relevant_facts;
	    gnum_relevant_facts++;
	  }
	}
      }
    }
  }
  /* fluents: collect all that are defined in initial state, plus
   * all that are assigned to by an effect of an action
   * (i.e. preconds poss. pos. due to reachability)
   *
   * first initialise fast access structures
   */
  for ( i = 0; i < gnum_functions; i++ ) {
    size =  1;
    for ( j = 0; j < gf_arity[i]; j++ ) {
      size *= gnum_constants;
    }
    lf_def[i] = ( int_pointer ) calloc( size, sizeof( int ) );
    lf_index[i] = ( int_pointer ) calloc( size, sizeof( int ) );
    for ( j = 0; j < size; j++ ) {
      lf_def[i][j] = 0;
      lf_index[i][j] = -1;
    }
  }
  /* from initial state, only those that are not static.
   */
  for ( fvs = gf_initial; fvs; fvs = fvs->next ) {
    lf = fvs->fluent.function;
    for ( j = 0; j < gf_arity[lf]; j++ ) {
      lf_args[j] = fvs->fluent.args[j];
    }
    /* this fn uses the same setup as fluent_adress();
     */
    adr = fluent_adress();
    if ( !gcmd_line.keep_optimization_vars &&
	 !occurs_in_pre_con_diffvarrhsexp_goal() ) {
      lf_index[lf][adr] = -17; /* just to be unique; will be queried below in action effects */
      continue;
    }
    if ( !lf_def[lf][adr] ) {
      lf_def[lf][adr] = 1;
      if ( gnum_relevant_fluents == MAX_RELEVANT_FLUENTS ) {
	printf("\ntoo many relevant fluents! increase MAX_RELEVANT_FLUENTS (currently %d)\n\n",
	       MAX_RELEVANT_FLUENTS);
	exit( 1 );
      }
      grelevant_fluents[gnum_relevant_fluents].function = lf;
      grelevant_fluents_name[gnum_relevant_fluents] = 
	( char * ) calloc( MAX_LENGTH, sizeof( char ) );
      strcpy( grelevant_fluents_name[gnum_relevant_fluents], gfunctions[lf] );
      for ( j = 0; j < gf_arity[lf]; j++ ) {
	grelevant_fluents[gnum_relevant_fluents].args[j] = lf_args[j];
	strcat( grelevant_fluents_name[gnum_relevant_fluents], "_" );
	strcat( grelevant_fluents_name[gnum_relevant_fluents], gconstants[lf_args[j]] );
      }
      lf_index[lf][adr] = gnum_relevant_fluents;
      gnum_relevant_fluents++;
    } else {
      printf("\n\nfluent ");
      print_Fluent( &(fvs->fluent) );
      printf(" defined twice in initial state! check input files\n\n");
      exit( 1 );
    }
  }
  /* from actions, all assigns (are non-static anyway)
   */
  for ( a = gactions; a; a = a->next ) {
    if ( a->norm_operator ) {
      no = a->norm_operator;
      for ( ne = no->effects; ne; ne = ne->next ) {
	for ( i = 0; i < ne->num_numeric_effects; i++ ) {
	  if ( ne->numeric_effects_neft[i] != ASSIGN ) continue;
	  lf = ne->numeric_effects_fluent[i].function;
	  for ( j = 0; j < gf_arity[lf]; j++ ) {
	    lf_args[j] = ( ne->numeric_effects_fluent[i].args[j] >= 0 ) ?
	      ne->numeric_effects_fluent[i].args[j] : 
	      a->inst_table[DECODE_VAR( ne->numeric_effects_fluent[i].args[j] )];
	  }
	  adr = fluent_adress();
	  if ( !lf_def[lf][adr] ) {
	    lf_def[lf][adr] = 1;
	    if ( gnum_relevant_fluents == MAX_RELEVANT_FLUENTS ) {
	      printf("\ntoo many relevant fluents! increase MAX_RELEVANT_FLUENTS (currently %d)\n\n",
		     MAX_RELEVANT_FLUENTS);
	      exit( 1 );
	    }
	    grelevant_fluents[gnum_relevant_fluents].function = lf;
	    grelevant_fluents_name[gnum_relevant_fluents] = 
	      ( char * ) calloc( MAX_LENGTH, sizeof( char ) );
	    strcpy( grelevant_fluents_name[gnum_relevant_fluents], gfunctions[lf] );
	    for ( j = 0; j < gf_arity[lf]; j++ ) {
	      grelevant_fluents[gnum_relevant_fluents].args[j] = lf_args[j];
	      strcat( grelevant_fluents_name[gnum_relevant_fluents], "_" );
	      strcat( grelevant_fluents_name[gnum_relevant_fluents], gconstants[lf_args[j]] );
	    }
	    lf_index[lf][adr] = gnum_relevant_fluents;
	    gnum_relevant_fluents++;
	  }
	}
      }
    } else {
      pa = a->pseudo_action;
      for ( pae = pa->effects; pae; pae = pae->next ) {
	for ( i = 0; i < pae->num_numeric_effects; i++ ) {
	  if ( pae->numeric_effects_neft[i] != ASSIGN ) continue;
	  lf = pae->numeric_effects_fluent[i].function;
	  for ( j = 0; j < gf_arity[lf]; j++ ) {
	    lf_args[j] = ( pae->numeric_effects_fluent[i].args[j] >= 0 ) ?
	      pae->numeric_effects_fluent[i].args[j] : 
	      a->inst_table[DECODE_VAR( pae->numeric_effects_fluent[i].args[j] )];
	  }
	  adr = fluent_adress();
	  if ( !lf_def[lf][adr] ) {
	    lf_def[lf][adr] = 1;
	    if ( gnum_relevant_fluents == MAX_RELEVANT_FLUENTS ) {
	      printf("\ntoo many relevant fluents! increase MAX_RELEVANT_FLUENTS (currently %d)\n\n",
		     MAX_RELEVANT_FLUENTS);
	      exit( 1 );
	    }
	    grelevant_fluents[gnum_relevant_fluents].function = lf;
	    grelevant_fluents_name[gnum_relevant_fluents] = 
	      ( char * ) calloc( MAX_LENGTH, sizeof( char ) );
	    strcpy( grelevant_fluents_name[gnum_relevant_fluents], gfunctions[lf] );
	    for ( j = 0; j < gf_arity[lf]; j++ ) {
	      grelevant_fluents[gnum_relevant_fluents].args[j] = lf_args[j];
	      strcat( grelevant_fluents_name[gnum_relevant_fluents], "_" );
	      strcat( grelevant_fluents_name[gnum_relevant_fluents], gconstants[lf_args[j]] );
	    }
	    lf_index[lf][adr] = gnum_relevant_fluents;
	    gnum_relevant_fluents++;
	  }
	}
      }
    }
  }

  if ( gcmd_line.display_info == 119 ) {
    printf("\n\nfacts selected as relevant:");
    for ( i = 0; i < gnum_relevant_facts; i++ ) {
      printf("\n%d: ", i);
      print_Fact( &(grelevant_facts[i]) );
    }
    printf("\n\nfluents selected as relevant:");
    for ( i = 0; i < gnum_relevant_fluents; i++ ) {
      printf("\n%d: ", i);
      print_Fluent( &(grelevant_fluents[i]) );
    }    
    printf("\n\n");
  }

  lnum_effects = 0;

  create_final_goal_state();
  create_final_initial_state();
  create_final_actions();

  if ( gcmd_line.keep_optimization_vars && gmetric != NULL ) {
    if ( !set_relevants_in_exp( &gmetric ) ) {
      if ( gcmd_line.display_info ) {
	printf("\nwarning: undefined fluent used in optimization expression. defaulting to plan length");
      }
      free_ExpNode( gmetric );
      gmetric = NULL;      
    }
  }

  if ( gcmd_line.display_info == 120 ) {
    printf("\n\nfinal domain representation is:\n\n");  

    for ( i = 0; i < gnum_operators; i++ ) {
      printf("\n\n------------------operator %s-----------\n\n", goperators[i]->name);
      for ( a = gactions; a; a = a->next ) {
	if ( ( !a->norm_operator &&
	       !a->pseudo_action ) ||
	     ( a->norm_operator && 
	       a->norm_operator->operator != goperators[i] ) ||
	     ( a->pseudo_action &&
	       a->pseudo_action->operator != goperators[i] ) ) {
	  continue;
	}
	print_Action( a );
      }
    }
    printf("\n\n--------------------GOAL REACHED ops-----------\n\n");
    for ( a = gactions; a; a = a->next ) {
      if ( !a->norm_operator &&
	   !a->pseudo_action ) {
	print_Action( a );
      }
    }

    printf("\n\nfinal initial state is:\n\n");
    print_State( ginitial_state );

    printf("\n\nfinal goal is:\n\n");
    for ( i = 0; i < gnum_logic_goal; i++ ) {
      print_ft_name( glogic_goal[i] );
      printf("\n");
    }
    for ( i = 0; i < gnum_numeric_goal; i++ ) {
      switch ( gnumeric_goal_comp[i] ) {
      case LE:
	printf("(< ");
	break;
      case LEQ:
	printf("(<= ");
	break;
      case EQ:
	printf("(= ");
	break;
      case GEQ:
	printf("(>= ");
	break;
      case GE:
	printf("(> ");
	break;
      default:
	printf("\nwrong comparator in gnumeric_goal %d\n\n", gnumeric_goal_comp[i]);
	exit( 1 );
      }
      print_ExpNode( gnumeric_goal_lh[i] );
      print_ExpNode( gnumeric_goal_rh[i] );
      printf(")\n");
    }

    if ( gmetric ) {
      printf("\n\nmetric is (minimize):\n");
      print_ExpNode( gmetric );
    } else {
      printf("\n\nmetric: none, i.e. plan length\n");
    }
  }

}



void create_final_goal_state( void )

{

  WffNode *w, *ww;
  int m, mn, i, adr;
  Action *tmp;

  if ( !set_relevants_in_wff( &ggoal ) ) {
    printf("\n\nff: goal accesses a fluent that will never have a defined value. Problem unsolvable.\n\n");
    exit( 1 );
  }
  cleanup_wff( &ggoal );

  if ( ggoal->connective == TRU ) {
    printf("\nff: goal can be simplified to TRUE. The empty plan solves it\n\n");
    exit( 1 );
  }
  if ( ggoal->connective == FAL ) {
    printf("\nff: goal can be simplified to FALSE. No plan will solve it\n\n");
    exit( 1 );
  }

  switch ( ggoal->connective ) {
  case OR:
    if ( gnum_relevant_facts == MAX_RELEVANT_FACTS ) {
      printf("\nincrease MAX_RELEVANT_FACTS! (current value: %d)\n\n",
	     MAX_RELEVANT_FACTS);
      exit( 1 );
    }
    grelevant_facts[gnum_relevant_facts].predicate = -3;
    gnum_relevant_facts++;
    for ( w = ggoal->sons; w; w = w->next ) {
      tmp = new_Action();
      if ( w->connective == AND ) {
	m = 0; mn = 0;
	for ( ww = w->sons; ww; ww = ww->next ) {
	  if ( ww->connective == ATOM ) m++;
	  if ( ww->connective == COMP ) mn++;
	}
	tmp->preconds = ( int * ) calloc( m, sizeof( int ) );
	tmp->numeric_preconds_comp = ( Comparator * ) calloc( mn, sizeof( Comparator ) );
	tmp->numeric_preconds_lh = ( ExpNode_pointer * ) calloc( mn, sizeof( ExpNode_pointer ) );
	tmp->numeric_preconds_rh = ( ExpNode_pointer * ) calloc( mn, sizeof( ExpNode_pointer ) );
	tmp->num_preconds = m;
	tmp->num_numeric_preconds = mn;
	m = 0; mn = 0;
	for ( ww = w->sons; ww; ww = ww->next ) {
	  if ( ww->connective == ATOM ) {
	    lp = ww->fact->predicate;
	    for ( i = 0; i < garity[lp]; i++ ) {
	      largs[i] = ww->fact->args[i];
	    }
	    adr = fact_adress();
	    tmp->preconds[m] = lindex[lp][adr];
	    m++;
	  }
	  if ( ww->connective == COMP ) {
	    tmp->numeric_preconds_comp[mn] = ww->comp;
	    tmp->numeric_preconds_lh[mn] = copy_Exp( ww->lh );
	    tmp->numeric_preconds_rh[mn] = copy_Exp( ww->rh );	    
	    mn++;
	  }
	}
      } else {
	if ( w->connective == ATOM ) {
	  tmp->preconds = ( int * ) calloc( 1, sizeof( int ) );
	  tmp->num_preconds = 1;
	  lp = w->fact->predicate;
	  for ( i = 0; i < garity[lp]; i++ ) {
	    largs[i] = w->fact->args[i];
	  }
	  adr = fact_adress();
	  tmp->preconds[0] = lindex[lp][adr];
	}
	if ( w->connective == COMP ) {
	  tmp->numeric_preconds_comp = ( Comparator * ) calloc( 1, sizeof( Comparator ) );
	  tmp->numeric_preconds_lh = ( ExpNode_pointer * ) calloc( 1, sizeof( ExpNode_pointer ) );
	  tmp->numeric_preconds_rh = ( ExpNode_pointer * ) calloc( 1, sizeof( ExpNode_pointer ) );
	  tmp->numeric_preconds_comp[0] = w->comp;
	  tmp->numeric_preconds_lh[0] = copy_Exp( w->lh );
	  tmp->numeric_preconds_rh[0] = copy_Exp( w->rh );
	  tmp->num_numeric_preconds = 1;
	}
      }
      tmp->effects = ( ActionEffect * ) calloc( 1, sizeof( ActionEffect ) );
      tmp->num_effects = 1;
      tmp->effects[0].conditions = NULL;
      tmp->effects[0].num_conditions = 0;
      tmp->effects[0].dels = NULL;
      tmp->effects[0].num_dels = 0;
      tmp->effects[0].adds = ( int * ) calloc( 1, sizeof( int ) );
      tmp->effects[0].adds[0] = gnum_relevant_facts - 1;
      tmp->effects[0].num_adds = 1;
      tmp->effects[0].numeric_conditions_comp = NULL;
      tmp->effects[0].numeric_conditions_lh = NULL;
      tmp->effects[0].numeric_conditions_rh = NULL;
      tmp->effects[0].num_numeric_conditions = 0;
      tmp->effects[0].numeric_effects_neft = NULL;
      tmp->effects[0].numeric_effects_fl = NULL;
      tmp->effects[0].numeric_effects_rh = NULL;
      tmp->effects[0].num_numeric_effects = 0;

      tmp->next = gactions;
      gactions = tmp;
      gnum_actions++;
      lnum_effects++;
    }
    glogic_goal = ( int * ) calloc( 1, sizeof( int ) );
    glogic_goal[0] = gnum_relevant_facts - 1;
    gnum_logic_goal = 1;
    break;
  case AND:
    m = 0; mn = 0;
    for ( w = ggoal->sons; w; w = w->next ) {
      if ( w->connective == ATOM ) m++;
      if ( w->connective == COMP ) mn++;
    }
    glogic_goal = ( int * ) calloc( m, sizeof( int ) );
    gnumeric_goal_comp = ( Comparator * ) calloc( mn, sizeof( Comparator ) );
    gnumeric_goal_lh = ( ExpNode_pointer * ) calloc( mn, sizeof( ExpNode_pointer ) );
    gnumeric_goal_rh = ( ExpNode_pointer * ) calloc( mn, sizeof( ExpNode_pointer ) );
    gnum_logic_goal = m;
    gnum_numeric_goal = mn;
    m = 0; mn = 0;
    for ( w = ggoal->sons; w; w = w->next ) {
      if ( w->connective == ATOM ) {
	lp = w->fact->predicate;
	for ( i = 0; i < garity[lp]; i++ ) {
	  largs[i] = w->fact->args[i];
	}
	adr = fact_adress();
	glogic_goal[m] = lindex[lp][adr];
	m++;
      }
      if ( w->connective == COMP ) {
	gnumeric_goal_comp[mn] = w->comp;
	gnumeric_goal_lh[mn] = copy_Exp( w->lh ); 
	gnumeric_goal_rh[mn] = copy_Exp( w->rh );
	mn++;
      }
    }
    break;
  case ATOM:
    glogic_goal = ( int * ) calloc( 1, sizeof( int ) );
    gnum_logic_goal = 1;
    lp = ggoal->fact->predicate;
    for ( i = 0; i < garity[lp]; i++ ) {
      largs[i] = ggoal->fact->args[i];
    }
    adr = fact_adress();
    glogic_goal[0] = lindex[lp][adr];
    break;
  case COMP:
    gnumeric_goal_comp = ( Comparator * ) calloc( 1, sizeof( Comparator ) );
    gnumeric_goal_lh = ( ExpNode_pointer * ) calloc( 1, sizeof( ExpNode_pointer ) );
    gnumeric_goal_rh = ( ExpNode_pointer * ) calloc( 1, sizeof( ExpNode_pointer ) );
    gnum_numeric_goal = 1;
    gnumeric_goal_comp[0] = ggoal->comp;
    gnumeric_goal_lh[0] = copy_Exp( ggoal->lh ); 
    gnumeric_goal_rh[0] = copy_Exp( ggoal->rh );
    break;
  default:
    printf("\n\nwon't get here: non COMP,ATOM,AND,OR in fully simplified goal\n\n");
    exit( 1 );
  }

}



Bool set_relevants_in_wff( WffNode **w )

{

  WffNode *i;
  int j, adr;

  switch ( (*w)->connective ) {
  case AND:
  case OR:
    for ( i = (*w)->sons; i; i = i->next ) {
      if ( !set_relevants_in_wff( &i ) ) {
	return FALSE;
      }
    }
    break;
  case ATOM:
    /* no equalities, as fully instantiated
     */
    lp = (*w)->fact->predicate;
    for ( j = 0; j < garity[lp]; j++ ) {
      largs[j] = (*w)->fact->args[j];
    }
    adr = fact_adress();

    if ( !lneg[lp][adr] ) {
      (*w)->connective = TRU;
      free( (*w)->fact );
      (*w)->fact = NULL;
      break;
    }
    if ( !lpos[lp][adr] ) {
      (*w)->connective = FAL;
      free( (*w)->fact );
      (*w)->fact = NULL;
      break;
    }
    break;
  case COMP:
    if ( !set_relevants_in_exp( &((*w)->lh) ) ||
	 !set_relevants_in_exp( &((*w)->rh) ) ) {
      return FALSE;
    }
    break;
  default:
    printf("\n\nwon't get here: non ATOM,OR,AND in goal set relevants\n\n");
    exit( 1 );
  }

  return TRUE;

}



Bool set_relevants_in_exp( ExpNode **n )

{

  int j, adr;

  /* can probably (for sure) forget about the simplification
   * stuff here because it's been done before.
   *
   * igual....
   */
  switch ( (*n)->connective ) {
  case AD:
    if ( !set_relevants_in_exp( &((*n)->leftson) ) ) return FALSE;
    if ( !set_relevants_in_exp( &((*n)->rightson) ) ) return FALSE;
    if ( (*n)->leftson->connective != NUMBER ||
	 (*n)->rightson->connective != NUMBER ) {
      break;
    }
    (*n)->connective = NUMBER;
    (*n)->value = (*n)->leftson->value + (*n)->rightson->value;
    free_ExpNode( (*n)->leftson );
    (*n)->leftson = NULL;
    free_ExpNode( (*n)->rightson );
    (*n)->rightson = NULL;
    break;
  case SU:
    if ( !set_relevants_in_exp( &((*n)->leftson) ) ) return FALSE;
    if ( !set_relevants_in_exp( &((*n)->rightson) ) ) return FALSE;
    if ( (*n)->leftson->connective != NUMBER ||
	 (*n)->rightson->connective != NUMBER ) {
      break;
    }
    (*n)->connective = NUMBER;
    (*n)->value = (*n)->leftson->value - (*n)->rightson->value;
    free_ExpNode( (*n)->leftson );
    (*n)->leftson = NULL;
    free_ExpNode( (*n)->rightson );
    (*n)->rightson = NULL;
    break;
  case MU:
    if ( !set_relevants_in_exp( &((*n)->leftson) ) ) return FALSE;
    if ( !set_relevants_in_exp( &((*n)->rightson) ) ) return FALSE;
    if ( (*n)->leftson->connective != NUMBER ||
	 (*n)->rightson->connective != NUMBER ) {
      break;
    }
    (*n)->connective = NUMBER;
    (*n)->value = (*n)->leftson->value * (*n)->rightson->value;
    free_ExpNode( (*n)->leftson );
    (*n)->leftson = NULL;
    free_ExpNode( (*n)->rightson );
    (*n)->rightson = NULL;
    break;
  case DI:
    if ( !set_relevants_in_exp( &((*n)->leftson) ) ) return FALSE;
    if ( !set_relevants_in_exp( &((*n)->rightson) ) ) return FALSE;
    if ( (*n)->leftson->connective != NUMBER ||
	 (*n)->rightson->connective != NUMBER ) {
      break;
    }
    if ( (*n)->rightson->value == 0 ) {
      /* kind of unclean: simply leave that in here;
       * we will later determine the right thing 
       * to do with it.
       */
      break;
    }
    (*n)->connective = NUMBER;
    (*n)->value = (*n)->leftson->value / (*n)->rightson->value;
    free_ExpNode( (*n)->leftson );
    (*n)->leftson = NULL;
    free_ExpNode( (*n)->rightson );
    (*n)->rightson = NULL;
    break;
  case MINUS:
    if ( !set_relevants_in_exp( &((*n)->son) ) ) return FALSE;
    if ( (*n)->son->connective != NUMBER ) break;
    (*n)->connective = NUMBER;
    (*n)->value = ((float) (-1)) * (*n)->son->value;
    free_ExpNode( (*n)->son );
    (*n)->son = NULL;
    break;    
  case NUMBER:
    break;
  case FHEAD:
    lf = (*n)->fluent->function;
    for ( j = 0; j < gf_arity[lf]; j++ ) {
      lf_args[j] = (*n)->fluent->args[j];
    }
    adr = fluent_adress();
    (*n)->fl = lf_index[lf][adr];
    free( (*n)->fluent );
    (*n)->fluent = NULL;
    if ( lf_index[lf][adr] == -1 ) {
      if ( lf == 0 ) {
	/* ATTENTION!! FUNCTION 0 IS TOTAL-TIME WHICH IS *ONLY* USED
	 * IN OPTIMIZATION EXPRESSION. GETS A SPECIAL TREATMENT
	 * IN THE RESPECTIVE FUNCTION IN SEARCH.C!!!!
	 *
	 * we remember it as fluent -2!!
	 */
	(*n)->fl = -2;
      } else {
	return FALSE;
      }
    }
    if ( lf_index[lf][adr] == -17 ) {
      /* we shouldn't get here!
       */
      return FALSE;
    }
    break;
  default:
    printf("\n\nset relevants in expnode: wrong specifier %d",
	   (*n)->connective);
    exit( 1 );
  }

  return TRUE;

}



void create_final_initial_state( void )

{

  Facts *f;
  int i, adr, fl;
  FluentValues *fvs;

  i = 0;
  for ( f = ginitial; f; f = f->next ) i++;
  /* we need space for transformation fluents to come!
   */
  make_state( &ginitial_state, i, MAX_RELEVANT_FLUENTS );

  for ( f = ginitial; f; f = f->next ) {
    lp = f->fact->predicate;
    for ( i = 0; i < garity[lp]; i++ ) {
      largs[i] = f->fact->args[i];
    }
    adr = fact_adress();
    if ( !lneg[lp][adr] ) {/* non deleted ini */
      continue;
    }
    ginitial_state.F[ginitial_state.num_F++] = lindex[lp][adr];
  }

  for ( fvs = gf_initial; fvs; fvs = fvs->next ) {
    lf = fvs->fluent.function;
    for ( i = 0; i < gf_arity[lf]; i++ ) {
      lf_args[i] = fvs->fluent.args[i];
    }
    adr = fluent_adress();
    fl = lf_index[lf][adr];
    if ( fl == -17 ) {
      /* skip this non-relevant guy!
       */
      continue;
    }
    ginitial_state.f_D[fl] = TRUE;
    ginitial_state.f_V[fl] = fvs->value;
  }

}



void create_final_actions( void )

{

  Action *a, *p, *t;
  NormOperator *no;
  NormEffect *ne;
  int i, j, adr;
  PseudoAction *pa;
  PseudoActionEffect *pae;
  ActionEffect *aa;
  Bool false_cond;

  gnum_effects = 0;
  a = gactions; p = NULL;
  while ( a ) {
    if ( a->norm_operator ) {
      /* action comes from an easy template NormOp
       */
      no = a->norm_operator;

      if ( no->num_preconds > 0 ) {
	a->preconds = ( int * ) calloc( no->num_preconds, sizeof( int ) );
      }
      a->num_preconds = 0;
      for ( i = 0; i < no->num_preconds; i++ ) {
	lp = no->preconds[i].predicate;
	for ( j = 0; j < garity[lp]; j++ ) {
	  largs[j] = ( no->preconds[i].args[j] >= 0 ) ?
	    no->preconds[i].args[j] : a->inst_table[DECODE_VAR( no->preconds[i].args[j] )];
	}
	adr = fact_adress();	
	/* preconds are lpos in all cases due to reachability analysis
	 */
	if ( !lneg[lp][adr] ) {
	  continue;
	}
	a->preconds[a->num_preconds++] = lindex[lp][adr];
      }

      /**************************NUMERIC PRECOND*************************/
      if ( no->num_numeric_preconds > 0 ) {
	a->numeric_preconds_comp = ( Comparator * ) 
	  calloc( no->num_numeric_preconds, sizeof( Comparator ) );
	a->numeric_preconds_lh = ( ExpNode_pointer * )
	  calloc( no->num_numeric_preconds, sizeof( ExpNode_pointer ) );
	a->numeric_preconds_rh = ( ExpNode_pointer * )
	  calloc( no->num_numeric_preconds, sizeof( ExpNode_pointer ) );
	a->num_numeric_preconds = 0;
      }
      for ( i = 0; i < no->num_numeric_preconds; i++ ) {
	a->numeric_preconds_comp[a->num_numeric_preconds] = no->numeric_preconds_comp[i];
	a->numeric_preconds_lh[a->num_numeric_preconds] = copy_Exp( no->numeric_preconds_lh[i] );
	instantiate_exp_by_action( &(a->numeric_preconds_lh[a->num_numeric_preconds]), a );
	if ( !set_relevants_in_exp( &(a->numeric_preconds_lh[a->num_numeric_preconds]) ) ) break;
	a->numeric_preconds_rh[a->num_numeric_preconds] = copy_Exp( no->numeric_preconds_rh[i] );
	instantiate_exp_by_action( &(a->numeric_preconds_rh[a->num_numeric_preconds]), a );
	if ( !set_relevants_in_exp( &(a->numeric_preconds_rh[a->num_numeric_preconds]) ) ) break;
	if ( a->numeric_preconds_lh[a->num_numeric_preconds]->connective == NUMBER &&
	     a->numeric_preconds_rh[a->num_numeric_preconds]->connective == NUMBER ) {
	  /* trivial numeric precond
	   */
	  if ( number_comparison_holds( a->numeric_preconds_comp[a->num_numeric_preconds],
					a->numeric_preconds_lh[a->num_numeric_preconds]->value,
					a->numeric_preconds_rh[a->num_numeric_preconds]->value ) ) {
	    /* true precond -> throw precond away. by not incrementing number of such.
	     */
	    free_ExpNode( a->numeric_preconds_lh[a->num_numeric_preconds] );
	    free_ExpNode( a->numeric_preconds_rh[a->num_numeric_preconds] );
	    continue;
	  } else {
	    /* false precond -> throw action away.
	     */
	    break;
	  }
	}
	a->num_numeric_preconds++;
      }
      if ( i < no->num_numeric_preconds ) {
	/* a precond accesses an undefined fluent, or is false -> remove action!
	 */
	gnum_actions--;
	if ( p ) {
	  p->next = a->next;
	  t = a;
	  a = a->next;
	  t->next = gtrash_actions;
	  gtrash_actions = t;
	} else {
	  gactions = a->next;
	  t = a;
	  a = a->next;
	  t->next = gtrash_actions;
	  gtrash_actions = t;
	}
	continue;
      }
      /**************************NUMERIC PRECOND-END*************************/

      /* and now for the effects
       */
      if ( a->num_effects > 0 ) {
	a->effects = ( ActionEffect * ) calloc( a->num_effects, sizeof( ActionEffect ) );
	for ( i = 0; i < a->num_effects; i++ ) {
	  a->effects[i].illegal = FALSE;
	  a->effects[i].removed = FALSE;

	  a->effects[i].id = gnum_effects++;
	}
      }
      a->num_effects = 0;
      for ( ne = no->effects; ne; ne = ne->next ) {
	aa = &(a->effects[a->num_effects]);

	if ( ne->num_conditions > 0 ) {
	  aa->conditions = ( int * ) calloc( ne->num_conditions, sizeof( int ) );
	}
	aa->num_conditions = 0;
	for ( i = 0; i < ne->num_conditions; i++ ) {
	  lp = ne->conditions[i].predicate;
	  for ( j = 0; j < garity[lp]; j++ ) {
	    largs[j] = ( ne->conditions[i].args[j] >= 0 ) ?
	      ne->conditions[i].args[j] : a->inst_table[DECODE_VAR( ne->conditions[i].args[j] )];
	  }
	  adr = fact_adress();
	  if ( !lpos[lp][adr] ) {/* condition not reachable: skip effect */
	    break;
	  }
	  if ( !lneg[lp][adr] ) {/* condition always true: skip it */
	    continue;
	  }
	  aa->conditions[aa->num_conditions++] = lindex[lp][adr];
	}
	if ( i < ne->num_conditions ) {/* found unreachable condition: free condition space */
	  free( aa->conditions );
	  continue;
	}

	/**************************NUMERIC COND*************************/
	if ( ne->num_numeric_conditions > 0 ) {
	  aa->numeric_conditions_comp = ( Comparator * ) 
	    calloc( ne->num_numeric_conditions, sizeof( Comparator ) );
	  aa->numeric_conditions_lh = ( ExpNode_pointer * )
	    calloc( ne->num_numeric_conditions, sizeof( ExpNode_pointer ) );
	  aa->numeric_conditions_rh = ( ExpNode_pointer * )
	    calloc( ne->num_numeric_conditions, sizeof( ExpNode_pointer ) );
	  for ( i = 0; i < ne->num_numeric_conditions; i++ ) {
	    aa->numeric_conditions_lh[i] = NULL;
	    aa->numeric_conditions_rh[i] = NULL;
	  }
	  aa->num_numeric_conditions = 0;
	}
	false_cond = FALSE;
	for ( i = 0; i < ne->num_numeric_conditions; i++ ) {
	  aa->numeric_conditions_comp[aa->num_numeric_conditions] = ne->numeric_conditions_comp[i];
	  aa->numeric_conditions_lh[aa->num_numeric_conditions] = copy_Exp( ne->numeric_conditions_lh[i] );
	  instantiate_exp_by_action( &(aa->numeric_conditions_lh[aa->num_numeric_conditions]), a );
	  if ( !set_relevants_in_exp( &(aa->numeric_conditions_lh[aa->num_numeric_conditions]) ) ) break;
	  aa->numeric_conditions_rh[aa->num_numeric_conditions] = copy_Exp( ne->numeric_conditions_rh[i] );
	  instantiate_exp_by_action( &(aa->numeric_conditions_rh[aa->num_numeric_conditions]), a );
	  if ( !set_relevants_in_exp( &(aa->numeric_conditions_rh[aa->num_numeric_conditions]) ) ) break;
	  if ( aa->numeric_conditions_lh[aa->num_numeric_conditions]->connective == NUMBER &&
	       aa->numeric_conditions_rh[aa->num_numeric_conditions]->connective == NUMBER ) {
	    /* trivial numeric condition
	     */
	    if ( number_comparison_holds( aa->numeric_conditions_comp[aa->num_numeric_conditions],
					  aa->numeric_conditions_lh[aa->num_numeric_conditions]->value,
					  aa->numeric_conditions_rh[aa->num_numeric_conditions]->value ) ) {
	      /* true cond -> throw cond away. by not incrementing number of such.
	       */
	      free_ExpNode( aa->numeric_conditions_lh[aa->num_numeric_conditions] );
	      free_ExpNode( aa->numeric_conditions_rh[aa->num_numeric_conditions] );
	      aa->numeric_conditions_lh[aa->num_numeric_conditions] = NULL;
	      aa->numeric_conditions_rh[aa->num_numeric_conditions] = NULL;
	      continue;
	    } else {
	      /* false cond -> throw effect away.
	       */
	      false_cond = TRUE;
	      break;
	    }
	  }
	  aa->num_numeric_conditions++;
	}
	if ( i < ne->num_numeric_conditions ) {
	  if ( false_cond ) {
	    /* false numeric cond: free what's been done so far, and skip effect
	     */
	    for ( i = 0; i <= aa->num_numeric_conditions; i++ ) {
	      free_ExpNode( aa->numeric_conditions_lh[i] );
	      free_ExpNode( aa->numeric_conditions_rh[i] );
	    }
	    free( aa->numeric_conditions_comp );
	    free( aa->numeric_conditions_lh );
	    free( aa->numeric_conditions_rh );
	    continue;/* next effect, without incrementing action counter */
	  } else {
	    /* numeric effect uses undefined fluent in condition -->
	     * THROW WHOLE ACTION AWAY! done by breaking out of the 
	     * effects loop, which will be catched below overall
	     * effect handling.
	     */
	    break;
	  }
	}
	/**************************NUMERIC COND - END*************************/

	/* now create the add and del effects.
	 */
	if ( ne->num_adds > 0 ) {
	  aa->adds = ( int * ) calloc( ne->num_adds, sizeof( int ) );
	}
	aa->num_adds = 0;
	for ( i = 0; i < ne->num_adds; i++ ) {
	  lp = ne->adds[i].predicate;
	  for ( j = 0; j < garity[lp]; j++ ) {
	    largs[j] = ( ne->adds[i].args[j] >= 0 ) ?
	      ne->adds[i].args[j] : a->inst_table[DECODE_VAR( ne->adds[i].args[j] )];
	  }
	  adr = fact_adress();
	  if ( !lneg[lp][adr] ) {/* effect always true: skip it */
	    continue;
	  }
	  aa->adds[aa->num_adds++] = lindex[lp][adr];
	}

	if ( ne->num_dels > 0 ) {
	  aa->dels = ( int * ) calloc( ne->num_dels, sizeof( int ) );
	}
	aa->num_dels = 0;
	for ( i = 0; i < ne->num_dels; i++ ) {
	  lp = ne->dels[i].predicate;
	  for ( j = 0; j < garity[lp]; j++ ) {
	    largs[j] = ( ne->dels[i].args[j] >= 0 ) ?
	      ne->dels[i].args[j] : a->inst_table[DECODE_VAR( ne->dels[i].args[j] )];
	  }
	  adr = fact_adress();
	  if ( !lpos[lp][adr] ) {/* effect always false: skip it */
	    continue;
	  }
	  /* NO CHECK FOR ADD \CAP DEL!!!!! -> ALLOWED BY SEMANTICS!!!
	   */
	  aa->dels[aa->num_dels++] = lindex[lp][adr];
	}
	if ( i < ne->num_dels ) break;

	/**************************NUMERIC EFFECTS*************************/
	if ( ne->num_numeric_effects > 0 ) {
	  aa->numeric_effects_neft = ( NumericEffectType * ) 
	    calloc( ne->num_numeric_effects, sizeof( NumericEffectType ) );
	  aa->numeric_effects_fl = ( int * )
	    calloc( ne->num_numeric_effects, sizeof( int ) );
	  aa->numeric_effects_rh = ( ExpNode_pointer * )
	    calloc( ne->num_numeric_effects, sizeof( ExpNode_pointer ) );
	  aa->num_numeric_effects = 0;
	}
	for ( i = 0; i < ne->num_numeric_effects; i++ ) {
	  lf = ne->numeric_effects_fluent[i].function;
	  for ( j = 0; j < gf_arity[lf]; j++ ) {
	    lf_args[j] = ( ne->numeric_effects_fluent[i].args[j] >= 0 ) ?
	      ne->numeric_effects_fluent[i].args[j] : 
	      a->inst_table[DECODE_VAR( ne->numeric_effects_fluent[i].args[j] )];
	  }
	  adr = fluent_adress();
	  /* if it's -17 then we know we must skip this numeric effect.
	   */
	  if ( lf_index[lf][adr] == -17 ) {
	    continue;
	  }
	  /* if it's -1, simply let it in --- if that effect appears, then 
	   * action is illegal, otherwise not.
	   */
	  aa->numeric_effects_fl[aa->num_numeric_effects] = lf_index[lf][adr];
	  if ( lf_index[lf][adr] == -1 ) aa->illegal = TRUE;
	  aa->numeric_effects_neft[aa->num_numeric_effects] = ne->numeric_effects_neft[i];
	  aa->numeric_effects_rh[aa->num_numeric_effects] = copy_Exp( ne->numeric_effects_rh[i] );
	  instantiate_exp_by_action( &(aa->numeric_effects_rh[aa->num_numeric_effects]), a );
	  if ( !set_relevants_in_exp( &(aa->numeric_effects_rh[aa->num_numeric_effects]) ) ) {
	    aa->illegal = TRUE;
	  }
	  if ( aa->illegal &&
	       aa->num_conditions == 0 &&
	       aa->num_numeric_conditions == 0 ) {
	    break;
	  }
	  /* that's it ???????????????? - !!
	   */
	  aa->num_numeric_effects++;
	}
	if ( i < ne->num_numeric_effects ) {
	  /* an unconditional illegal effekt
	   */
	  break;
	}
	/**************************NUMERIC EFFECTS - END*************************/

	/* this effect is OK. go to next one in NormOp.
	 */
	a->num_effects++;
	lnum_effects++;
      }
      if ( ne ) {
	/* we get here if one effect was faulty
	 */
	gnum_actions--;
	if ( p ) {
	  p->next = a->next;
	  t = a;
	  a = a->next;
	  t->next = gtrash_actions;
	  gtrash_actions = t;
	} else {
	  gactions = a->next;
	  t = a;
	  a = a->next;
	  t->next = gtrash_actions;
	  gtrash_actions = t;
	}
      } else {
	p = a;
	a = a->next;
      }
      continue;
    }
    /**********************************second half: hard operators --> pseudo actions******************/
    if ( a->pseudo_action ) {
      /* action is result of a PseudoAction
       */
      pa = a->pseudo_action;
      if ( pa->num_preconds > 0 ) {
	a->preconds = ( int * ) calloc( pa->num_preconds, sizeof( int ) );
      }
      a->num_preconds = 0;
      for ( i = 0; i < pa->num_preconds; i++ ) {
	lp = pa->preconds[i].predicate;
	for ( j = 0; j < garity[lp]; j++ ) {
	  largs[j] = pa->preconds[i].args[j];
	}
	adr = fact_adress();
	/* preconds are lpos in all cases due to reachability analysis
	 */
	if ( !lneg[lp][adr] ) {
	  continue;
	}	
	a->preconds[a->num_preconds++] = lindex[lp][adr];
      }

      /**************************NUMERIC PRECOND*************************/
      if ( pa->num_numeric_preconds > 0 ) {
	a->numeric_preconds_comp = ( Comparator * ) 
	  calloc( pa->num_numeric_preconds, sizeof( Comparator ) );
	a->numeric_preconds_lh = ( ExpNode_pointer * )
	  calloc( pa->num_numeric_preconds, sizeof( ExpNode_pointer ) );
	a->numeric_preconds_rh = ( ExpNode_pointer * )
	  calloc( pa->num_numeric_preconds, sizeof( ExpNode_pointer ) );
	a->num_numeric_preconds = 0;
      }
      for ( i = 0; i < pa->num_numeric_preconds; i++ ) {
	a->numeric_preconds_comp[a->num_numeric_preconds] = pa->numeric_preconds_comp[i];
	a->numeric_preconds_lh[a->num_numeric_preconds] = copy_Exp( pa->numeric_preconds_lh[i] );
	if ( !set_relevants_in_exp( &(a->numeric_preconds_lh[a->num_numeric_preconds]) ) ) break;
	a->numeric_preconds_rh[a->num_numeric_preconds] = copy_Exp( pa->numeric_preconds_rh[i] );
	if ( !set_relevants_in_exp( &(a->numeric_preconds_rh[a->num_numeric_preconds]) ) ) break;
	a->num_numeric_preconds++;
      }
      if ( i < pa->num_numeric_preconds ) {
	/* a precond accesses an undefined fluent -> remove action!
	 */
	gnum_actions--;
	if ( p ) {
	  p->next = a->next;
	  t = a;
	  a = a->next;
	  t->next = gtrash_actions;
	  gtrash_actions = t;
	} else {
	  gactions = a->next;
	  t = a;
	  a = a->next;
	  t->next = gtrash_actions;
	  gtrash_actions = t;
	}
	continue;
      }
      /**************************NUMERIC PRECOND-END*************************/

      /* and now for the effects
       */
      if ( a->num_effects > 0 ) {
	a->effects = ( ActionEffect * ) calloc( a->num_effects, sizeof( ActionEffect ) );
	for ( i = 0; i < a->num_effects; i++ ) {
	  a->effects[i].illegal = FALSE;
	  a->effects[i].removed = FALSE;
	}
      }
      a->num_effects = 0;
      for ( pae = pa->effects; pae; pae = pae->next ) {
	aa = &(a->effects[a->num_effects]);

	if ( pae->num_conditions > 0 ) {
	  aa->conditions = ( int * ) calloc( pae->num_conditions, sizeof( int ) );
	}
	aa->num_conditions = 0;
	for ( i = 0; i < pae->num_conditions; i++ ) {
	  lp = pae->conditions[i].predicate;
	  for ( j = 0; j < garity[lp]; j++ ) {
	    largs[j] = pae->conditions[i].args[j];
	  }
	  adr = fact_adress();
	  if ( !lpos[lp][adr] ) {/* condition not reachable: skip effect */
	    break;
	  }
	  if ( !lneg[lp][adr] ) {/* condition always true: skip it */
	    continue;
	  }
	  aa->conditions[aa->num_conditions++] = lindex[lp][adr];
	}
	if ( i < pae->num_conditions ) {/* found unreachable condition: free condition space */
	  free( aa->conditions );
	  continue;
	}

	/**************************NUMERIC COND*************************/
	if ( pae->num_numeric_conditions > 0 ) {
	  aa->numeric_conditions_comp = ( Comparator * ) 
	    calloc( pae->num_numeric_conditions, sizeof( Comparator ) );
	  aa->numeric_conditions_lh = ( ExpNode_pointer * )
	    calloc( pae->num_numeric_conditions, sizeof( ExpNode_pointer ) );
	  aa->numeric_conditions_rh = ( ExpNode_pointer * )
	    calloc( pae->num_numeric_conditions, sizeof( ExpNode_pointer ) );
	  for ( i = 0; i < pae->num_numeric_conditions; i++ ) {
	    aa->numeric_conditions_lh[i] = NULL;
	    aa->numeric_conditions_rh[i] = NULL;
	  }
	  aa->num_numeric_conditions = 0;
	}
	for ( i = 0; i < pae->num_numeric_conditions; i++ ) {
	  aa->numeric_conditions_comp[aa->num_numeric_conditions] = pae->numeric_conditions_comp[i];
	  aa->numeric_conditions_lh[aa->num_numeric_conditions] = copy_Exp( pae->numeric_conditions_lh[i] );
	  if ( !set_relevants_in_exp( &(aa->numeric_conditions_lh[aa->num_numeric_conditions]) ) ) break;
	  aa->numeric_conditions_rh[aa->num_numeric_conditions] = copy_Exp( pae->numeric_conditions_rh[i] );
	  if ( !set_relevants_in_exp( &(aa->numeric_conditions_rh[aa->num_numeric_conditions]) ) ) break;
	  aa->num_numeric_conditions++;
	}
	if ( i < pae->num_numeric_conditions ) {
	  /* numeric effect uses undefined fluent in condition -->
	   * THROW WHOLE ACTION AWAY! done by breaking out of the 
	   * effects loop, which will be catched below overall
	   * effect handling.
	   */
	  break;
	}
	/**************************NUMERIC COND - END*************************/

	/* now create the add and del effects.
	 */
	if ( pae->num_adds > 0 ) {
	  aa->adds = ( int * ) calloc( pae->num_adds, sizeof( int ) );
	}
	aa->num_adds = 0;
	for ( i = 0; i < pae->num_adds; i++ ) {
	  lp = pae->adds[i].predicate;
	  for ( j = 0; j < garity[lp]; j++ ) {
	    largs[j] = pae->adds[i].args[j];
	  }
	  adr = fact_adress();
	  if ( !lneg[lp][adr] ) {/* effect always true: skip it */
	    continue;
	  }
	  aa->adds[aa->num_adds++] = lindex[lp][adr];
	}

	if ( pae->num_dels > 0 ) {
	  aa->dels = ( int * ) calloc( pae->num_dels, sizeof( int ) );
	}
	aa->num_dels = 0;
	for ( i = 0; i < pae->num_dels; i++ ) {
	  lp = pae->dels[i].predicate;
	  for ( j = 0; j < garity[lp]; j++ ) {
	    largs[j] = pae->dels[i].args[j];
	  }
	  adr = fact_adress();
	  if ( !lpos[lp][adr] ) {/* effect always false: skip it */
	    continue;
	  }
	  aa->dels[aa->num_dels++] = lindex[lp][adr];
	}
	if ( i < pae->num_dels ) break;

	/**************************NUMERIC EFFECTS*************************/
	if ( pae->num_numeric_effects > 0 ) {
	  aa->numeric_effects_neft = ( NumericEffectType * ) 
	    calloc( pae->num_numeric_effects, sizeof( NumericEffectType ) );
	  aa->numeric_effects_fl = ( int * )
	    calloc( pae->num_numeric_effects, sizeof( int ) );
	  aa->numeric_effects_rh = ( ExpNode_pointer * )
	    calloc( pae->num_numeric_effects, sizeof( ExpNode_pointer ) );
	  aa->num_numeric_effects = 0;
	}
	for ( i = 0; i < pae->num_numeric_effects; i++ ) {
	  aa->numeric_effects_neft[aa->num_numeric_effects] = pae->numeric_effects_neft[i];
	  lf = pae->numeric_effects_fluent[i].function;
	  for ( j = 0; j < gf_arity[lf]; j++ ) {
	    lf_args[j] = pae->numeric_effects_fluent[i].args[j];
	    if ( lf_args[j] < 0 ) {
	      printf("\n\nuninstantiated affected fluent in final actions! debug me.\n\n");
	      exit( 1 );
	    }
	  }
	  adr = fluent_adress();
	  /* if it's -1, simply let it in --- if that effect appears, then 
	   * action is illegal, otherwise not.
	   */
	  aa->numeric_effects_fl[i] = lf_index[lf][adr];
	  if ( lf_index[lf][adr] == -1 ) aa->illegal = TRUE;
	  aa->numeric_effects_rh[aa->num_numeric_effects] = copy_Exp( pae->numeric_effects_rh[i] );
	  if ( !set_relevants_in_exp( &(aa->numeric_effects_rh[aa->num_numeric_effects]) ) ) {
	    aa->illegal = TRUE;
	  }
	  if ( aa->illegal &&
	       aa->num_conditions == 0 &&
	       aa->num_numeric_conditions == 0 ) {
	    break;
	  }
	  /* that's it ???????????????? - !!
	   */
	  aa->num_numeric_effects++;
	}
	if ( i < pae->num_numeric_effects ) {
	  /* an unconditional illegal effekt
	   */
	  break;
	}
	/**************************NUMERIC EFFECTS - END*************************/

	/* this effect is OK. go to next one in PseudoAction.
	 */
	a->num_effects++;
	lnum_effects++;
      }
      if ( pae ) {
	/* we get here if one effect was faulty
	 */
	gnum_actions--;
	if ( p ) {
	  p->next = a->next;
	  t = a;
	  a = a->next;
	  t->next = gtrash_actions;
	  gtrash_actions = t;
	} else {
	  gactions = a->next;
	  t = a;
	  a = a->next;
	  t->next = gtrash_actions;
	  gtrash_actions = t;
	}
      } else {
	p = a;
	a = a->next;
      }
      continue;
    }/* end of if clause for PseudoAction */
    /* if action was neither normop, nor pseudo action determined,
     * then it is an artificial action due to disjunctive goal
     * conditions.
     *
     * these are already in final form.
     */
    p = a;
    a = a->next;
  }/* endfor all actions ! */

  /* set the ids.
   */
  j = 0;
  for ( a = gactions; a; a = a->next ) {
    a->id = j++;
  }

}



void instantiate_exp_by_action( ExpNode **n, Action *a )

{

  int j, f, k, h;
  Bool ok;

  switch ( (*n)->connective ) {
  case AD:
    instantiate_exp_by_action( &((*n)->leftson), a );
    instantiate_exp_by_action( &((*n)->rightson), a );
    if ( (*n)->leftson->connective != NUMBER ||
	 (*n)->rightson->connective != NUMBER ) {
      break;
    }
    (*n)->connective = NUMBER;
    (*n)->value = (*n)->leftson->value + (*n)->rightson->value;
    free_ExpNode( (*n)->leftson );
    (*n)->leftson = NULL;
    free_ExpNode( (*n)->rightson );
    (*n)->rightson = NULL;
    break;
  case SU:
    instantiate_exp_by_action( &((*n)->leftson), a );
    instantiate_exp_by_action( &((*n)->rightson), a );
    if ( (*n)->leftson->connective != NUMBER ||
	 (*n)->rightson->connective != NUMBER ) {
      break;
    }
    (*n)->connective = NUMBER;
    (*n)->value = (*n)->leftson->value - (*n)->rightson->value;
    free_ExpNode( (*n)->leftson );
    (*n)->leftson = NULL;
    free_ExpNode( (*n)->rightson );
    (*n)->rightson = NULL;
    break;
  case MU:
    instantiate_exp_by_action( &((*n)->leftson), a );
    instantiate_exp_by_action( &((*n)->rightson), a );
    if ( (*n)->leftson->connective != NUMBER ||
	 (*n)->rightson->connective != NUMBER ) {
      break;
    }
    (*n)->connective = NUMBER;
    (*n)->value = (*n)->leftson->value * (*n)->rightson->value;
    free_ExpNode( (*n)->leftson );
    (*n)->leftson = NULL;
    free_ExpNode( (*n)->rightson );
    (*n)->rightson = NULL;
    break;
  case DI:
    instantiate_exp_by_action( &((*n)->leftson), a );
    instantiate_exp_by_action( &((*n)->rightson), a );
    if ( (*n)->leftson->connective != NUMBER ||
	 (*n)->rightson->connective != NUMBER ) {
      break;
    }
    if ( (*n)->rightson->value == 0 ) {
      /* kind of unclean: simply leave that in here;
       * we will later determine the right thing 
       * to do with it.
       */
      break;
    }
    (*n)->connective = NUMBER;
    (*n)->value = (*n)->leftson->value / (*n)->rightson->value;
    free_ExpNode( (*n)->leftson );
    (*n)->leftson = NULL;
    free_ExpNode( (*n)->rightson );
    (*n)->rightson = NULL;
    break;
  case MINUS:
    instantiate_exp_by_action( &((*n)->son), a );
    if ( (*n)->son->connective != NUMBER ) break;
    (*n)->connective = NUMBER;
    (*n)->value = ((float) (-1)) * (*n)->son->value;
    free_ExpNode( (*n)->son );
    (*n)->son = NULL;
    break;    
  case NUMBER:
    break;
  case FHEAD:
    f = (*n)->fluent->function;
    ok = TRUE;
    for ( j = 0; j < gf_arity[f]; j++ ) {
      h = ( (*n)->fluent->args[j] < 0 ) ?
	a->inst_table[DECODE_VAR( (*n)->fluent->args[j] )] : (*n)->fluent->args[j];
      if ( h < 0 ) {
	ok = FALSE;
      } else {
	(*n)->fluent->args[j] = h;
      }
    }
    if ( !ok ) {
      printf("\n\nnon-instantiated fluent in final actiona! debug me!!\n\n");
      exit( 1 );
    }
    if ( gis_changed[f] ) break;
    for ( j = 0; j < gnum_initial_function[f]; j++ ) {
      for ( k = 0; k < gf_arity[f]; k++ ) {
	if ( ginitial_function[f][j].fluent.args[k] !=
	     (*n)->fluent->args[k] ) break;
      }
      if ( k < gf_arity[f] ) continue;
      (*n)->connective = NUMBER;
      (*n)->value = ginitial_function[f][j].value;
      break;
    }
    break;
  default:
    printf("\n\ninst. exp by action: wrong specifier %d",
	   (*n)->connective);
    exit( 1 );
  }

}



/* this fn checks if a fluent occurs anywhere in a prec
 * an eff cond, a rhs of a num eff on a diff fluent, or
 * the goal. every bit as ugly as its name.
 */
Bool occurs_in_pre_con_diffvarrhsexp_goal( void )

{

  Action *a;
  NormOperator *no;
  NormEffect *ne;
  PseudoAction *pa;
  PseudoActionEffect *pae;

  int i, j, arg;

  /* first go through the actions.
   */
  for ( a = gactions; a; a = a->next ) {
    if ( a->norm_operator ) {
      no = a->norm_operator;

      /* precondition
       */
      for ( i = 0; i < no->num_numeric_preconds; i++ ) {
	if ( occurs_in_exp(a, no->numeric_preconds_lh[i]) ) {
	  return TRUE;
	}
	if ( occurs_in_exp(a, no->numeric_preconds_rh[i]) ) {
	  return TRUE;
	}
      }

      /* effects
       */
      for ( ne = no->effects; ne; ne = ne->next ) {

	/* conditions
	 */
	for ( i = 0; i < ne->num_numeric_conditions; i++ ) {
	  if ( occurs_in_exp(a, ne->numeric_conditions_lh[i]) ) {
	    return TRUE;
	  }
	  if ( occurs_in_exp(a, ne->numeric_conditions_rh[i]) ) {
	    return TRUE;
	  }
	}

	/* num effects
	 */
	for ( i = 0; i < ne->num_numeric_effects; i++ ) {
	  /* check if this is on a *different* fluent.
	   */
	  if ( ne->numeric_effects_fluent[i].function == lf ) {
	    for ( j = 0; j < gf_arity[lf]; j++ ) {
	      arg = ( ne->numeric_effects_fluent[i].args[j] >= 0 ) ?
		ne->numeric_effects_fluent[i].args[j] : 
		a->inst_table[DECODE_VAR( ne->numeric_effects_fluent[i].args[j] )];
	      if ( arg != lf_args[j] ) {
		break;
	      }
	    }
	    if ( j == gf_arity[lf] ) {
	      /* this is the fluent itself! skip this num eff.
	       */
	      continue;
	    }
	  }
	  if ( occurs_in_exp(a, ne->numeric_effects_rh[i]) ) {
	    return TRUE;
	  }
	}
      }

      continue;
    }

    if ( a->pseudo_action ) {
      /* action is result of a PseudoAction;
       * NOTE: in difference to normop actions, pseudoactions are fully
       * instantiated!
       */
      pa = a->pseudo_action;

      /* precondition
       */
      for ( i = 0; i < pa->num_numeric_preconds; i++ ) {
	if ( occurs_in_exp(NULL, pa->numeric_preconds_lh[i]) ) {
	  return TRUE;
	}
	if ( occurs_in_exp(NULL, pa->numeric_preconds_rh[i]) ) {
	  return TRUE;
	}
      }

      /* effects
       */
      for ( pae = pa->effects; pae; pae = pae->next ) {

	/* conditions
	 */
	for ( i = 0; i < pae->num_numeric_conditions; i++ ) {
	  if ( occurs_in_exp(NULL, pae->numeric_conditions_lh[i]) ) {
	    return TRUE;
	  }
	  if ( occurs_in_exp(NULL, pae->numeric_conditions_rh[i]) ) {
	    return TRUE;
	  }
	}

	/* num effects
	 */
	for ( i = 0; i < pae->num_numeric_effects; i++ ) {
	  /* check if this is on a *different* fluent.
	   */
	  if ( pae->numeric_effects_fluent[i].function == lf ) {
	    for ( j = 0; j < gf_arity[lf]; j++ ) {
	      arg = pae->numeric_effects_fluent[i].args[j];
	      if ( arg < 0 ) {
		printf("\nrel check: <0 arg in pseudo action?\n\n");
		exit( 1 );
	      }
	      if ( arg != lf_args[j] ) {
		break;
	      }
	    }
	    if ( j == gf_arity[lf] ) {
	      /* this is the fluent itself! skip this num eff.
	       */
	      continue;
	    }
	  }
	  if ( occurs_in_exp(NULL, pae->numeric_effects_rh[i]) ) {
	    return TRUE;
	  }
	}
      }

      continue;
    }

    printf("\nnon normop neither pseudo act in relevance check?\n\n");
    exit( 1 );
  }

  /* goal?
   */
  if ( occurs_in_wff(ggoal) ) {
    return TRUE;
  }

  /* finally..!
   */
  return FALSE;

}



Bool occurs_in_wff( WffNode *w )

{

  WffNode *i;

  switch ( w->connective ) {
  case AND:
  case OR:
    for ( i = w->sons; i; i = i->next ) {
      if ( occurs_in_wff(i) ) {
	return TRUE;
      }
    }
    break;
  case ATOM:
    break;
  case COMP:
    if ( occurs_in_exp(NULL, w->lh) ||
	 occurs_in_exp(NULL, w->rh) ) {
      return TRUE;
    }
    break;
  default:
    printf("\n\nwon't get here: non ATOM,OR,AND,COMP in occurs in wff\n\n");
    exit( 1 );
  }

  return FALSE;

}



/* a gives the instantiation table -- none if NULL
 */
Bool occurs_in_exp( Action *a, ExpNode *n )

{

  int i, arg;

  switch ( n->connective ) {
  case AD:
  case SU:
  case MU:
  case DI:
    if ( occurs_in_exp(a, n->leftson ) ||
	 occurs_in_exp(a, n->rightson ) ) {
      return TRUE;
    }
    break;
  case MINUS:
    if ( occurs_in_exp(a, n->son ) ) {
      return TRUE;
    }
    break;    
  case NUMBER:
    break;
  case FHEAD:
    if ( n->fluent->function != lf ) {
      break;
    }
    for ( i = 0; i < gf_arity[lf]; i++ ) {
      arg = n->fluent->args[i];
      if ( arg < 0 ) {
	if ( !a ) {
	  printf("\nneg arg in occurs in exp with null act?\n\n");
	  exit( 1 );
	}
	arg = a->inst_table[DECODE_VAR( n->fluent->args[i] )];
      }
      if ( arg != lf_args[i] ) {
	break;
      }
    }
    if ( i == gf_arity[lf] ) {
      return TRUE;
    }
    break;
  default:
    printf("\n\noccurs in exp: wrong specifier %d", n->connective);
    exit( 1 );
  }

  return FALSE;

}























/***********************************************************
 * EXPLICIT REPRESENTATIONS OF CONSTRAINTS AND PSIS        *
 ***********************************************************/


















void collect_relevant_constraints_and_psis( void )

{

  int psi[MAX_PSI_CONSTRAINTS], num_psi;

  Action *ia;
  ActionEffect *ie;
  int i, j, k;



  /* 1. collect constraints.
   */
  for ( ia = gactions; ia; ia = ia->next ) {

    /* not really important, just has been chosen so: the max nr of constraints in any
     * stored psi is preset. not a big deal, that number should be very low typically.
     */
    if ( ia->num_numeric_preconds >= MAX_PSI_CONSTRAINTS ) {
      printf("\ntoo many prec constraints, %d. increase  MAX_PSI_CONSTRAINTS.\n\n", 
	     ia->num_numeric_preconds);
      exit( 1 );
    }
    ia->pre_constraint_id = ( int * ) calloc(ia->num_numeric_preconds, sizeof( int ));
    for ( i = 0; i < ia->num_numeric_preconds; i++ ) {
      ia->pre_constraint_id[i] = collect_constraint(ia->numeric_preconds_lh[i], 
						    ia->numeric_preconds_comp[i], 
						    ia->numeric_preconds_rh[i]);
      for ( j = 0; j < i; j++ ) {
	if ( ia->pre_constraint_id[i] == ia->pre_constraint_id[j] ) {
	  printf("\naction prec contains same constraint twice? check input.\n\n");
	  exit( 1 );
	}
      }
    }

    for ( i = 0; i < ia->num_effects; i++ ) {
      ie = &(ia->effects[i]);

      if ( ia->num_numeric_preconds + ie->num_numeric_conditions >= MAX_PSI_CONSTRAINTS ) {
	printf("\ntoo many prec+eff constraints, %d. increase  MAX_PSI_CONSTRAINTS.\n\n", 
	       ia->num_numeric_preconds + ie->num_numeric_conditions);
	exit( 1 );
      }
      ie->con_constraint_id = ( int * ) calloc(ie->num_numeric_conditions, sizeof( int ));
      for ( j = 0; j < ie->num_numeric_conditions; j++ ) {
	ie->con_constraint_id[j] = collect_constraint(ie->numeric_conditions_lh[j], 
						      ie->numeric_conditions_comp[j], 
						      ie->numeric_conditions_rh[j]);
	for ( k = 0; k < ia->num_numeric_preconds; k++ ) {
	  if ( ie->con_constraint_id[j] == ia->pre_constraint_id[k] ) {
	    printf("\neffect con contains action prec constraint? check input.\n\n");
	    exit( 1 );
	  }
	}
	for ( k = 0; k < j; k++ ) {
	  if ( ie->con_constraint_id[j] == ie->con_constraint_id[k] ) {
	    printf("\neffect con contains same constraint twice? check input.\n\n");
	    exit( 1 );
	  }
	}
      }
    }
  }

  if ( gnum_numeric_goal >= MAX_PSI_CONSTRAINTS ) {
    printf("\ntoo many goal constraints, %d. increase  MAX_PSI_CONSTRAINTS.\n\n", 
	   gnum_numeric_goal);
    exit( 1 );
  }
  ggoal_constraint_id = ( int * ) calloc(gnum_numeric_goal, sizeof( int ));
  for ( i = 0; i < gnum_numeric_goal; i++ ) {
    ggoal_constraint_id[i] = collect_constraint(gnumeric_goal_lh[i], 
						gnumeric_goal_comp[i], 
						gnumeric_goal_rh[i]);
    for ( j = 0; j < i; j++ ) {
      if ( ggoal_constraint_id[i] == ggoal_constraint_id[j] ) {
	printf("\ngoal contains same constraint twice? check input.\n\n");
	exit( 1 );
      }
    }
  }
  

  
  /* 2. collect psis.
   */
  for ( ia = gactions; ia; ia = ia->next ) {
    if ( ia->num_numeric_preconds == 0 ) {
      ia->pre_psi_id = -1;
    } else {
      ia->pre_psi_id = collect_psi(ia->pre_constraint_id, ia->num_numeric_preconds);
    }

    for ( i = 0; i < ia->num_effects; i++ ) {
      ie = &(ia->effects[i]);

      if ( ia->num_numeric_preconds + ie->num_numeric_conditions == 0 ) {
	ie->con_psi_id = -1;
	continue;
      }

      /* we conjoin the cons with the pres!
       * this is more natural in RPG bulding, where
       * an eff is instantiated only with those tuples that
       * satisfy this entire conjunction.
       */
      num_psi = 0;
      for ( j = 0; j < ia->num_numeric_preconds; j++ ) {
	psi[num_psi++] = ia->pre_constraint_id[j];
      }
      for ( j = 0; j < ie->num_numeric_conditions; j++ ) {
	psi[num_psi++] = ie->con_constraint_id[j];
      }

      ie->con_psi_id = collect_psi(psi, num_psi);
    }
  }

  if ( gnum_numeric_goal == 0 ) {
    ggoal_psi_id = -1;
  } else {
    ggoal_psi_id = collect_psi(ggoal_constraint_id, gnum_numeric_goal);
  }

  if ( gcmd_line.display_info == 121 || gcmd_line.debug ) {
    printf("\ncollected constraints:");
    for ( i = 0; i < gnum_relevant_constraints; i++ ) {
      printf("\n%d: ", i);
      print_ExpNode(grelevant_constraints_lhs[i]);
      printf(" ");
      print_comparator(grelevant_constraints_comp[i]);
      printf(" ");
      print_ExpNode(grelevant_constraints_rhs[i]);
    }

    printf("\n\ncollected psis:");
    for ( i = 0; i < gnum_relevant_psis; i++ ) {
      printf("\n%d:", i);
      for ( j = 0; j < grelevant_psis[i]->num_psi; j++ ) {
	printf(" %d", grelevant_psis[i]->psi[j]);
      }
    }

    printf("\n\npsi actions:");
    for ( ia = gactions; ia; ia = ia->next ) {
      print_psi_Action(ia);
    }

    printf("\n\npsi goal: %d", ggoal_psi_id);

    fflush(stdout);
  }

}



int collect_constraint(ExpNode *lhs, Comparator comp, ExpNode *rhs)

{

  int i;

  for ( i = 0; i < gnum_relevant_constraints; i++ ) {
    if ( same_expression(grelevant_constraints_lhs[i], lhs) &&
	 grelevant_constraints_comp[i] == comp &&
	 same_expression(grelevant_constraints_rhs[i], rhs) ) {
      return i;
    }
  }

  if ( i >= MAX_RELEVANT_CONSTRAINTS ) {
    printf("\n\ntoo manny different constraints, %d. increase MAX_RELEVANT_CONSTRAINTS.\n\n",
	   i);
    exit( 1 );
  }
  grelevant_constraints_lhs[i] = lhs;
  grelevant_constraints_comp[i] = comp;
  grelevant_constraints_rhs[i] = rhs;
  gnum_relevant_constraints++;

  return i;

}



int collect_psi(int *psi, int num_psi)

{

  int i, j, k;

  for ( i = 0; i < gnum_relevant_psis; i++ ) {
    if ( grelevant_psis[i]->num_psi != num_psi ) {
      continue;
    }
    
    for ( j = 0; j < grelevant_psis[i]->num_psi; j++ ) {
      for ( k = 0; k < num_psi; k++ ) {
	if ( grelevant_psis[i]->psi[j] == psi[k] ) {
	  break;
	}
      }
      if ( k == num_psi ) {
	/* this constraint is not in here
	 */
	break;
      }
    }
    if ( j < grelevant_psis[i]->num_psi ) {
      /* found a "bad" one.
       */
      continue;
    }

    return i;
  }

  if ( i >= MAX_RELEVANT_PSIS ) {
    printf("\n\ntoo manny different constraint conjunctions, %d. increase MAX_RELEVANT_PSIS.\n\n",
	   i);
    exit( 1 );
  }

  grelevant_psis[i] = new_Psi();
  grelevant_psis[i]->num_psi = num_psi;
  for ( j = 0; j < num_psi; j++ ) {
    grelevant_psis[i]->psi[j] = psi[j];
  }
  gnum_relevant_psis++;

  return i;

}



/* just take syntactic identity.
 */
Bool same_expression(ExpNode *exp1, ExpNode *exp2)

{

  if ( !exp1 && !exp2 ) {
    return TRUE;
  }

  if ( !exp1 && exp2 ) {
    return FALSE;
  }

  if ( exp1 && !exp2 ) {
    return FALSE;
  }

  if ( exp1->connective != exp2->connective ) {
    return FALSE;
  }

  switch ( exp1->connective ) {
  case FHEAD:
    if ( exp1->fl != exp2->fl ) {
      return FALSE;
    }
    break;
  case NUMBER:
    if ( exp1->value != exp2->value ) {
      return FALSE;
    }
    break;
  case MINUS:
    if ( !same_expression(exp1->son, exp2->son) )  {
      return FALSE;
    }
    break;
  case AD:
  case SU:
  case MU:
  case DI:
    if ( !same_expression(exp1->leftson, exp2->leftson) ||
	 !same_expression(exp1->rightson, exp2->rightson) )  {
      return FALSE;
    }
    break;
  default:
    printf("\nunknown exp connective.\n\n");
    exit( 1 );
  }

  return TRUE;
}


