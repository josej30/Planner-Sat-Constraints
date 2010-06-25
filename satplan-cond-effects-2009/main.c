

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
 * File: main.c
 * Description: The main routine for the num2sat planner.
 *
 * Author: Joerg Hoffmann 2006
 * 
 *********************************************************************/ 








#include "num2sat.h"

#include "memory.h"
#include "output.h"

#include "parse.h"

#include "inst_pre.h"
#include "inst_easy.h"
#include "inst_hard.h"
#include "inst_final.h"

#include "RPG.h"
#include "RPGvaluetuples.h"

#include "CNF.h"
#include "HCNF.h"











/*
 *  ----------------------------- GLOBAL VARIABLES ----------------------------
 */












/*******************
 * GENERAL HELPERS *
 *******************/








/* used to time the different stages of the planner
 */
float gtempl_time = 0, greach_time = 0, grelev_time = 0;
float gRPG_time = 0, gCNF_time = 0, gSAT_time = 0;


/* the command line inputs
 */
struct _command_line gcmd_line;

/* number of states that got heuristically evaluated
 */
int gevaluated_states = 0;

/* maximal depth of breadth first search
 */
int gmax_search_depth = 0;





/***********
 * PARSING *
 ***********/







/* used for pddl parsing, flex only allows global variables
 */
int gbracket_count;
char *gproblem_name;

/* The current input line number
 */
int lineno = 1;

/* The current input filename
 */
char *gact_filename;

/* The pddl domain name
 */
char *gdomain_name = NULL;

/* loaded, uninstantiated operators
 */
PlOperator *gloaded_ops = NULL;

/* stores initials as fact_list 
 */
PlNode *gorig_initial_facts = NULL;

/* not yet preprocessed goal facts
 */
PlNode *gorig_goal_facts = NULL;

/* axioms as in UCPOP before being changed to ops
 */
PlOperator *gloaded_axioms = NULL;

/* the types, as defined in the domain file
 */
TypedList *gparse_types = NULL;

/* the constants, as defined in domain file
 */
TypedList *gparse_constants = NULL;

/* the predicates and their arg types, as defined in the domain file
 */
TypedListList *gparse_predicates = NULL;

/* the functions and their arg types, as defined in the domain file
 */
TypedListList *gparse_functions = NULL;

/* the objects, declared in the problem file
 */
TypedList *gparse_objects = NULL;

/* the metric
 */
Token gparse_optimization;
ParseExpNode *gparse_metric = NULL;


/* connection to instantiation ( except ops, goal, initial )
 */

/* all typed objects 
 */
FactList *gorig_constant_list = NULL;

/* the predicates and their types
 */
FactList *gpredicates_and_types = NULL;

/* the functions and their types
 */
FactList *gfunctions_and_types = NULL;












/*****************
 * INSTANTIATING *
 *****************/









/* global arrays of constant names,
 *               type names (with their constants),
 *               predicate names,
 *               predicate aritys,
 *               defined types of predicate args
 */
Token gconstants[MAX_CONSTANTS];
int gnum_constants = 0;
Token gtype_names[MAX_TYPES];
int gtype_consts[MAX_TYPES][MAX_TYPE];
Bool gis_member[MAX_CONSTANTS][MAX_TYPES];
int gtype_size[MAX_TYPES];
int gnum_types = 0;
Token gpredicates[MAX_PREDICATES];
int garity[MAX_PREDICATES];
int gpredicates_args_type[MAX_PREDICATES][MAX_ARITY];
int gnum_predicates = 0;
Token gfunctions[MAX_FUNCTIONS];
int gf_arity[MAX_FUNCTIONS];
int gfunctions_args_type[MAX_FUNCTIONS][MAX_ARITY];
int gnum_functions = 0;





/* the domain in integer (Fact) representation
 */
Operator_pointer goperators[MAX_OPERATORS];
int gnum_operators = 0;
Fact *gfull_initial;
int gnum_full_initial = 0;
FluentValue *gfull_fluents_initial;
int gnum_full_fluents_initial = 0;
WffNode *ggoal = NULL;

ExpNode *gmetric = NULL;



/* stores inertia - information: is any occurence of the predicate
 * added / deleted in the uninstantiated ops ?
 */
Bool gis_added[MAX_PREDICATES];
Bool gis_deleted[MAX_PREDICATES];


/* for functions we *might* want to say, symmetrically, whether it is
 * increased resp. decreased at all.
 *
 * that is, however, somewhat involved because the right hand
 * sides can be arbirtray expressions, so we have no guarantee
 * that increasing really does adds to a functions value...
 *
 * thus (for the time being), we settle for "is the function changed at all?"
 */
Bool gis_changed[MAX_FUNCTIONS];



/* splitted initial state:
 * initial non static facts,
 * initial static facts, divided into predicates
 * (will be two dimensional array, allocated directly before need)
 */
Facts *ginitial = NULL;
int gnum_initial = 0;
Fact **ginitial_predicate;
int *gnum_initial_predicate;

/* same thing for functions
 */
FluentValues *gf_initial;
int gnum_f_initial = 0;
FluentValue **ginitial_function;
int *gnum_initial_function;



/* the type numbers corresponding to any unary inertia
 */
int gtype_to_predicate[MAX_PREDICATES];
int gpredicate_to_type[MAX_TYPES];

/* (ordered) numbers of types that new type is intersection of
 */
TypeArray gintersected_types[MAX_TYPES];
int gnum_intersected_types[MAX_TYPES];



/* splitted domain: hard n easy ops
 */
Operator_pointer *ghard_operators;
int gnum_hard_operators;
NormOperator_pointer *geasy_operators;
int gnum_easy_operators;



/* so called Templates for easy ops: possible inertia constrained
 * instantiation constants
 */
EasyTemplate *geasy_templates;
int gnum_easy_templates;



/* first step for hard ops: create mixed operators, with conjunctive
 * precondition and arbitrary effects
 */
MixedOperator *ghard_mixed_operators;
int gnum_hard_mixed_operators;



/* hard ''templates'' : pseudo actions
 */
PseudoAction_pointer *ghard_templates;
int gnum_hard_templates;




/* store the final "relevant facts"
 */
Fact grelevant_facts[MAX_RELEVANT_FACTS];
int gnum_relevant_facts = 0;
int gnum_pp_facts = 0;
/* store the "relevant fluents"
 */
Fluent grelevant_fluents[MAX_RELEVANT_FLUENTS];
int gnum_relevant_fluents = 0;
Token grelevant_fluents_name[MAX_RELEVANT_FLUENTS];

/* NEW: also collect all expressions mentioned, as well as 
 * all relevant *conjunctions* of expressions. this will be
 * convenient for tuple gathering during RPG (used also in CNF), since
 * we need to do this only once for each relevant expression/conjunction,
 * rather than repeat it every time such a construct occurs.
 */


/* array of expression node pointers;
 * ID == array index will be used to identify
 */
ExpNode_pointer grelevant_constraints_lhs[MAX_RELEVANT_CONSTRAINTS];
Comparator grelevant_constraints_comp[MAX_RELEVANT_CONSTRAINTS];
ExpNode_pointer grelevant_constraints_rhs[MAX_RELEVANT_CONSTRAINTS];
int gnum_relevant_constraints = 0;

Psi_pointer grelevant_psis[MAX_RELEVANT_PSIS];
int gnum_relevant_psis = 0;




/* the final actions and problem representation
 */
Action *gactions = NULL;
int gnum_actions;
int gnum_effects = 0;/* so we know how many effects there are in total */
State ginitial_state;
int *glogic_goal = NULL;
int gnum_logic_goal = 0;
Comparator *gnumeric_goal_comp = NULL;
ExpNode_pointer *gnumeric_goal_lh = NULL, *gnumeric_goal_rh = NULL;
int gnum_numeric_goal = 0;
/* the ID representation of this!
 */
int *ggoal_constraint_id;
/* and the ID of the overall psi!
 */
int ggoal_psi_id;

/* direct numeric goal access
 */
Comparator *gnumeric_goal_direct_comp;
float *gnumeric_goal_direct_c;



/* to avoid memory leaks; too complicated to identify
 * the exact state of the action to throw away (during construction),
 * memory gain not worth the implementation effort.
 */
Action *gtrash_actions = NULL;


/* The RPG!
 */

RPGlayer *gRPG;



/* The CNF!
 *
 * including end pointer so we can conveniently keep appending more clauses
 * at the end.
 */
CNF *gCNF, *gCNFend;
/* also keep track of the nrs of vars and clauses.
 */
int gCNFnumvars, gCNFnumclauses;


/* here, removed goal clauses will be chained in.
 * just to avoid memory leaks, and to not do freeing,
 * which sometimes behaves very oddly.
 */
CNF *gCNFtrash, *gCNFtrashend;





/* The Hybrid CNF!
 *
 * including end pointer so we can conveniently keep appending more clauses
 * at the end.
 */
HCNF *gHCNF, *gHCNFend;
/* also keep track of the nrs of vars and clauses.
 */
int gHCNFnumvars, gHCNFnumclauses;


/* here, removed goal clauses will be chained in.
 * just to avoid memory leaks, and to not do freeing,
 * which sometimes behaves very oddly.
 */
HCNF *gHCNFtrash, *gHCNFtrashend;






/* these here are for communication with the main functions in RPGvaluetuples.c
 */

/* RPG_get_valuetuples
 * takes an int array of constraint ids,
 * and outs out a list of value tuples into
 * this dynamically allocated list here:
 */
RPGvaluetuple *gget_valuetuples_result;
int gget_valuetuples_num_result;



/* RPG_get_valuetuples_exp
 *
 * takes a psi id (may be -1) and an expression,
 * and outs synchronized lists of value tuples and values,
 * with the meaning that value[i] arises for exp under valuetuple[i].
 * the tuples are all in this layer that satisfy the constraints.
 * relies on that the value tuples for psi are assembled 
 * in the RPG layer already.
 */
RPGvaluetuple *gget_valuetuples_exp_result_vt;
RPGvalue *gget_valuetuples_exp_result_v;
int gget_valuetuples_exp_num_result;


/*
  For mutex in memory-less
 */
char only_keep_mutex_with[MAX_LENGTH];




/* for time-out
 */
struct tms gTstart, gTend;













/*
 *  ----------------------------- HEADERS FOR PARSING ----------------------------
 * ( fns defined in the scan-* files )
 */







void get_fct_file_name( char *filename );
void load_ops_file( char *filename );
void load_fct_file( char *filename );
void load_mutex2ignore_file( char *filename );


char num2satpath[] = "~/num2sat";
char here[] = ".";








/*
 *  ----------------------------- MAIN ROUTINE ----------------------------
 */





struct tms lstart, lend;



Bool lfound_plan;


int main( int argc, char *argv[] )

{

  /* resulting name for ops file
   */
  char ops_file[MAX_LENGTH] = "";
  /* same for fct file 
   */
  char fct_file[MAX_LENGTH] = "";
  
  /* for calls to outside programs, eg zchaff.
   */
  char command[MAX_LENGTH];
  char command2[MAX_LENGTH]; /* for trying another path */
  /* for getting their answer.
   */
  FILE *SATRES;

  /* sat solver data.
   */
  int sat;
  float sat_rtime;
  int nractions = -1;

  struct tms start, end;

  RPGlayer *t, *tpp;

  Bool goalreached;

  char c;
  int linecount;

/*   int time; */



  times ( &lstart );

  printf("\n\n");
  system("rm CNF");
  system("rm SATRES");
  printf("\n\n");
  fflush(stdout);

  /* command line treatment
   */
  if ( argc == 1 || ( argc == 2 && *++argv[0] == '?' ) ) {
    ff_usage();
    exit( 1 );
  }
  if ( !process_command_line( argc, argv ) ) {
    ff_usage();
    exit( 1 );
  }


  /* make file names
   */

  /* one input name missing
   */
  if ( !gcmd_line.ops_file_name || 
       !gcmd_line.fct_file_name ) {
    fprintf(stdout, "\nff: two input files needed\n\n");
    ff_usage();      
    exit( 1 );
  }
  /* add path info, complete file names will be stored in
   * ops_file and fct_file 
   */
  sprintf(ops_file, "%s%s", gcmd_line.path, gcmd_line.ops_file_name);
  sprintf(fct_file, "%s%s", gcmd_line.path, gcmd_line.fct_file_name);


  /* parse the input files
   */

  /* start parse & instantiation timing
   */
  times( &start );
  /* domain file (ops)
   */
  if ( gcmd_line.display_info >= 1 ) {
    printf("\nff: parsing domain file");
  } 
  /* it is important for the pddl language to define the domain before 
   * reading the problem 
   */
  load_ops_file( ops_file );
  /* problem file (facts)
   */  
  if ( gcmd_line.display_info >= 1 ) {
    printf(" ... done.\nff: parsing problem file"); 
  }
  load_fct_file( fct_file );
  if ( gcmd_line.display_info >= 1 ) {
    printf(" ... done.\n\n");
  }

  /*
    Load token of mutex2ignore
   */
  if( gcmd_line.mutex2ignore_file_name[0] != '\0' )
    load_mutex2ignore_file( gcmd_line.mutex2ignore_file_name );

  /* This is needed to get all types.
   */
  build_orig_constant_list();

  /* last step of parsing: see if it's an ADL domain!
   */
  if ( !make_adl_domain() ) {
    printf("\nff: this is not an ADL problem!");
    printf("\n    can't be handled by this version.\n\n");
    exit( 1 );
  }


  /* now instantiate operators;
   */


  /**************************
   * first do PREPROCESSING * 
   **************************/

  /* start by collecting all strings and thereby encoding 
   * the domain in integers.
   */
  encode_domain_in_integers();

  /* inertia preprocessing, first step:
   *   - collect inertia information
   *   - split initial state into
   *        - arrays for individual predicates
   *        - arrays for all static relations
   *        - array containing non - static relations
   */
  do_inertia_preprocessing_step_1();

  /* normalize all PL1 formulae in domain description:
   * (goal, preconds and effect conditions)
   *   - simplify formula
   *   - expand quantifiers
   *   - NOTs down
   */
  normalize_all_wffs();

  /* translate negative preconds: introduce symmetric new predicate
   * NOT-p(..) (e.g., not-in(?ob) in briefcaseworld)
   */
  translate_negative_preconds();

  /* split domain in easy (disjunction of conjunctive preconds)
   * and hard (non DNF preconds) part, to apply 
   * different instantiation algorithms
   */
  split_domain();

  /***********************************************
   * PREPROCESSING FINISHED                      *
   *                                             *
   * NOW MULTIPLY PARAMETERS IN EFFECTIVE MANNER *
   ***********************************************/

  build_easy_action_templates();
  build_hard_action_templates();

  times( &end );
  TIME( gtempl_time );

  times( &start );

  /* perform reachability analysis in terms of relaxed 
   * fixpoint
   */
  perform_reachability_analysis();

  times( &end );
  TIME( greach_time );

  times( &start );

  /* collect the relevant facts and build final domain
   * and problem representations.
   */
  collect_relevant_facts_and_fluents();

  times( &end );
  TIME( grelev_time );


  /* for num2sat, SKIP LNF AND, WITH THAT, GCONN STRUCTURES!!!
   *
   * reason: LNF is not needed for the CNF encodings, and the RPG is
   *         built only once so optimizations are not time critical.
   *
   *         LNF introduces a huge overhead, and creates many variables
   *         (e.g. n^2 vs n for pre-LNF, in jugs) which would have to be
   *         filtered for the input ones, anyway.
   *
   * RPG sets off on these data structures:
   * extern Action *gactions;
   * extern int gnum_actions;
   * extern State ginitial_state;
   * extern int *glogic_goal;
   * extern int gnum_logic_goal;
   * extern Comparator *gnumeric_goal_comp;
   * extern ExpNode_pointer *gnumeric_goal_lh, *gnumeric_goal_rh;
   * extern int gnum_numeric_goal;
   */

  /* instead, do some additional pre-processing to collect all different 
   * constraints, and all different conjunctions psi of constraints.
   * needed to get a natural implementation of collecting value tuples
   * for all such constructs.
   */
  collect_relevant_constraints_and_psis();



  /* that is done. let's go.
   *
   * NOTE that keeping track of the RPG layers in here
   * isn't just a coincidence. It's made so that we can use these same 
   * functions to build another RPG if we want to, eg. one that's
   * modified to greedily estimate the variable domains instead of
   * enumerating them completely.
   */


  /* separating CNF and Hybrid CNF methods completely,
   * though they got a large overlap.
   * reason: looks nicer, and mayb at some point
   * we're gonna use a different RPG for hybrid.
   */

  /* just to avoid "might be used uninitialized" message
   */
  tpp = NULL;

  if ( gcmd_line.CNFencoding == 0 ||
       gcmd_line.CNFencoding == 1 ) {
    /* propositional CNF!
     */
    times( &start );
    gRPG = new_RPGlayer();
    t = RPG_initialize(gRPG);
    times( &end );
    TIME( gRPG_time );
    TIMECHECK;
    if ( gcmd_line.display_info ) {
      RPG_PV_statistics(t);
      fflush(stdout);
    }
    
    times( &start );
    gCNF = new_CNF();
    gCNFend = gCNF;
    gCNFnumvars = 0;
    gCNFnumclauses = 0;
    CNF_initialize(t, 
		   &gCNFend,
		   &gCNFnumvars,
		   &gCNFnumclauses);
    times( &end );
    TIME( gCNF_time );
    TIMECHECK;
    if ( gcmd_line.display_info ) {
      CNF_statistics(t, gCNF, gCNFnumvars, gCNFnumclauses);
      fflush(stdout);
    }
    
    goalreached = FALSE;
    while ( TRUE ) {
      times( &start );
      tpp = RPG_extend(t);
      times( &end );
      TIME( gRPG_time );
      TIMECHECK;
      if ( gcmd_line.display_info ) {
	RPG_AE_statistics(t);
	RPG_PV_statistics(tpp);
	fflush(stdout);
      }
      
      times( &start );
      CNF_extend(t, 
		 &gCNFend,
		 &gCNFnumvars,
		 &gCNFnumclauses);
      times( &end );
      TIME( gCNF_time );
      TIMECHECK;
      if ( gcmd_line.display_info ) {
	CNF_statistics(tpp, gCNF, gCNFnumvars, gCNFnumclauses); 
	fflush(stdout);
      }

      if ( !goalreached && !RPG_satisfiesgoal(tpp) ) {
	t = tpp;
	continue;
      }
      
      if ( !goalreached ) {
	if ( gcmd_line.display_info ) {
	  printf("\nGoal reached at %d!", tpp->t); 
	  fflush(stdout);
	}
	goalreached = TRUE;
      }
      
      CNF_get_goal(tpp, 
		   &gCNFend, 
		   &gCNFnumclauses);

      CNF_output(gCNF, gCNFnumvars, gCNFnumclauses, tpp->t);
      TIMECHECK;
      if ( gcmd_line.debug && gcmd_line.dCNF ) {
	CNF_print(gRPG, gCNF, gCNFnumvars, gCNFnumclauses);
	printf("\n\n");
/* 	exit( 0 ); */
      }
      if ( gcmd_line.CNFsolver == 0 ) {
	sprintf(command, "%s/solvers/minisat/MiniSat_v1.14/minisat CNF",
		num2satpath);
	sprintf(command2, "%s/solvers/minisat/MiniSat_v1.14/minisat CNF",
		here);
      }
      if ( gcmd_line.CNFsolver == 1 ) {
	sprintf(command, "%s/solvers/zchaff/zchaff CNF", num2satpath);
	sprintf(command2, "%s/solvers/zchaff/zchaff CNF", here);
      }
      if ( gcmd_line.CNFsolver == 2 ) { /* OJO: que no hagan falta dos comandos: -m y -s 2 */
	/* minisat */
	CNF_print_act_table(gRPG, "action-table");
	sprintf(command, "%s/solvers/minisat+mutex.py CNF action-table %s m", 
		num2satpath,
		gcmd_line.mutex2ignore_file_name );
	sprintf(command2, "%s/solvers/minisat+mutex.py CNF action-table %s m", 
		here,
		gcmd_line.mutex2ignore_file_name );
      }
      if ( gcmd_line.CNFsolver == 3 ) { 
	/* zchaff */
	CNF_print_act_table(gRPG, "action-table");
	sprintf(command, "%s/solvers/minisat+mutex.py CNF action-table %s z", 
		num2satpath,
		gcmd_line.mutex2ignore_file_name );
	sprintf(command2, "%s/solvers/minisat+mutex.py CNF action-table %s z", 
		here,
		gcmd_line.mutex2ignore_file_name );
      }
      if ( gcmd_line.display_info ) {
	printf("\nInvoking SAT solver, command:");
	printf("\n%s", command);
	printf("\n");
	fflush(stdout);
      }
      if( system( command ) )
	{
	  printf("failed with path %s, trying with %s\n", num2satpath, here);
	  printf("\nInvoking SAT solver, command:");
	  printf("\n%s", command2);
	  printf("\n");
	  fflush(stdout);
	  system( command2 );
	}
      if ( (SATRES = fopen( "SATRES", "r" )) == NULL ) {
	printf("\nSATRES file not present. Failure!\n\n");
	exit( 0 );
      }
      fscanf(SATRES, "%d %f\n", &sat, &sat_rtime);
      gSAT_time += sat_rtime;
      TIMECHECK;
      if ( sat ) {
	break;
      }
      fclose(SATRES);
/*       system("rm CNF"); */
/*       system("rm SATRES"); */
      
      CNF_retract_goal(tpp, 
		       &gCNFend, 
		       &gCNFnumclauses);
      
      t = tpp;
    } /* endwhile main planning loop */

    if ( gcmd_line.display_info ) {
      nractions = CNF_output_plan(SATRES, gRPG, gCNFnumvars);
      fflush(stdout);
    }
    fclose(SATRES);
/*     system("rm CNF"); */
/*     system("rm SATRES"); */
  } /* endif propositional CNF requested */





  if ( gcmd_line.CNFencoding == 2 ||
       gcmd_line.CNFencoding == 3 ) {
    /* Hybrid CNF!
     */
    times( &start );
    gRPG = new_RPGlayer();
    t = RPG_initialize(gRPG);
    times( &end );
    TIME( gRPG_time );
    TIMECHECK;
    if ( gcmd_line.display_info ) {
      RPG_PV_statistics(t);
      fflush(stdout);
    }
    
    times( &start );
    gHCNF = new_HCNF();
    gHCNFend = gHCNF;
    gHCNFnumvars = 0;
    gHCNFnumclauses = 0;
    HCNF_initialize(t, 
		    &gHCNFend,
		    &gHCNFnumvars,
		    &gHCNFnumclauses);
    times( &end );
    TIME( gCNF_time );
    TIMECHECK;
    if ( gcmd_line.display_info ) {
      HCNF_statistics(t, gHCNF, gHCNFnumvars, gHCNFnumclauses);
      fflush(stdout);
    }
    
    goalreached = FALSE;
    while ( TRUE ) {
      times( &start );
      tpp = RPG_extend(t);
      times( &end );
      TIME( gRPG_time );
      TIMECHECK;
      if ( gcmd_line.display_info ) {
	RPG_AE_statistics(t);
	RPG_PV_statistics(tpp);
	fflush(stdout);
      }
      
      times( &start );
      HCNF_extend(t, 
		  &gHCNFend,
		  &gHCNFnumvars,
		  &gHCNFnumclauses);
      times( &end );
      TIME( gCNF_time );
      TIMECHECK;
      if ( gcmd_line.display_info ) {
	HCNF_statistics(tpp, gHCNF, gHCNFnumvars, gHCNFnumclauses);
	fflush(stdout);
      }
      
      if ( !goalreached && !RPG_satisfiesgoal(tpp) ) {
	t = tpp;
	continue;
      }
      
      if ( !goalreached ) {
	if ( gcmd_line.display_info ) {
	  printf("\nGoal reached at %d!", tpp->t);
	  fflush(stdout);
	}
	goalreached = TRUE;
      }
      
      HCNF_get_goal(tpp, 
		    &gHCNFend, 
		    &gHCNFnumclauses);

      HCNF_output(gRPG, gHCNF, gHCNFnumvars, gHCNFnumclauses, tpp->t);
      TIMECHECK;
      if ( gcmd_line.debug && gcmd_line.dHCNF ) {
	HCNF_print(gRPG, gHCNF, gHCNFnumvars, gHCNFnumclauses);
	printf("\n\n");
	exit( 0 );
      }

      sprintf(command, "%s/solvers/mathsat/mathsat-3.3.1/mathsat CNF > SATRES", num2satpath);
      sprintf(command2, "%s/solvers/mathsat/mathsat-3.3.1/mathsat CNF > SATRES", here);
      if ( gcmd_line.display_info ) {
	printf("\nInvoking MATHSAT solver, command:");
	printf("\n%s", command);
	printf("\n");
	fflush(stdout);
      }
      if( system( command ) )
	{
	  printf("failed with path %s, trying with %s\n", num2satpath, here);
	  system( command2 );
	}
      if ( (SATRES = fopen( "SATRES", "r" )) == NULL ) {
	printf("\nSATRES file not present. Failure!\n\n");
	exit( 0 );
      }
      /* read in MATHSAT's output. looks like:
       * Result = 1
       * TSTP Exit Status: SAT
       *
       * # -------------------------------------------------
       * # User time   : 0.020 s
       * # System time : 0.019 s
       * # Total time  : 0.039 s
       */
      fscanf(SATRES, "Result = %d\n", &sat);
      linecount = 0;
      while ( TRUE ) {
	c = fgetc(SATRES);
	if ( c == '\n') {
	  linecount++;
	  if ( linecount == 5 ) {
	    break;
	  }
	}
      }
      fscanf(SATRES, "# Total time  : %f s\n", &sat_rtime);
      
      gSAT_time += sat_rtime;
      TIMECHECK;
      if ( sat ) {
	if ( gcmd_line.display_info ) {
	  printf("\nSAT! %f sec. Plan found.", sat_rtime);
	  fflush(stdout);
	}
	break;
      } else {
	if ( gcmd_line.display_info ) {
	  printf("\nUNSAT! %f sec. Iterate.", sat_rtime);
	  fflush(stdout);
	}
      }
      fclose(SATRES);
      system("rm CNF");
      system("rm SATRES");
      
      HCNF_retract_goal(tpp, 
			&gHCNFend, 
			&gHCNFnumclauses);
      
      t = tpp;
    } /* endwhile main planning loop */
    fclose(SATRES);
    system("rm CNF");
    system("rm SATRES");
  } /* endif hybrid CNF requested */



  if ( !tpp ) {
    printf("\ntpp NULL at plan info output?\n\n");
    exit( 1 );
  }
  if ( gcmd_line.display_info ) {
    output_planner_info(gRPG, nractions);
  }



  printf("\n\n");
  exit( 0 );

}











/*
 *  ----------------------------- HELPING FUNCTIONS ----------------------------
 */

/* Load tokens for ignoring mutex
 */

char *mutex2ignore[MAX_OPERATORS+1];

void load_mutex2ignore_file( char *filename )
{ 
  FILE* MUTEX2IGNORE; 
  int num = 0;
  int read = 0;

  if ( (MUTEX2IGNORE = fopen( filename, "r" )) == NULL ) {
    printf("\n%s file not present. Failure!\n\n",filename);
    exit( 0 );
  }
  
  fscanf( MUTEX2IGNORE, "%d\n", &num );
  while ( !feof( MUTEX2IGNORE ) && read < num ) {
    if ( ferror( MUTEX2IGNORE ) )
      {
	printf("\nError reading file %s.\n\n",filename);
	exit( 0 );
      }
    mutex2ignore[read] = (char*) calloc( MAX_LENGTH+10, sizeof(char) );
    fscanf( MUTEX2IGNORE, "%s\n", mutex2ignore[read] );
    printf( "Reading mutex %s\n", mutex2ignore[read]);
    read++;
  }
  fclose( MUTEX2IGNORE );
}



void output_planner_info( RPGlayer *rpg, int nractions )

{

  FILE *out;

  RPGlayer *t, *goalt;
  RPGvalue *v;
  int i, num;

  
  for ( goalt = rpg; goalt->next; goalt = goalt->next );

  printf( "\n\ntime spent: %7.2f seconds instantiating %d easy, %d hard action templates", 
	  gtempl_time, gnum_easy_templates, gnum_hard_mixed_operators );
  printf( "\n            %7.2f seconds reachability analysis, yielding %d facts and %d actions", 
	  greach_time, gnum_pp_facts, gnum_actions );
  printf( "\n            %7.2f seconds creating final representation with %d relevant facts, %d relevant fluents", 
	  grelev_time, gnum_relevant_facts, gnum_relevant_fluents );
  printf( "\n            %7.2f seconds building RPG",
	  gRPG_time );
  printf( "\n            %7.2f seconds building CNF",
	  gCNF_time );
  printf( "\n            %7.2f seconds SAT solving",
	  gSAT_time );
  printf( "\n            %7.2f seconds total time, parallel plan length %d nr actions %d", 
	  gtempl_time + greach_time + grelev_time + gRPG_time + gCNF_time + gSAT_time,
	  goalt->t, nractions);

  if ( gcmd_line.data ) {
    if ( (out = fopen( "DATA", "w" )) == NULL ) {
      printf("\nDATA file no se puede write\n\n");
      exit( 1 );
    }

    /* for comparison to naive discretization, in some domains:
     * count nr of values in RPG!
     */
    num = 0;
    for ( t = rpg->next; t; t = t->next ) {
      for ( i = 0; i < gnum_relevant_fluents; i++ ) {
	for ( v = t->V[i]->next; v; v = v->next ) {
	  num++;
	}
      }
    }

    fprintf(out, "%.2f %d %d %d %.2f %.2f\n", 
	    gtempl_time + greach_time + grelev_time + gRPG_time + gCNF_time + gSAT_time,
	    nractions,
	    goalt->t,
	    num,
	    gRPG_time,
	    gCNF_time);
    
    fclose( out );
  }

}



void ff_usage( void )

{

  printf("\nusage of num2sat:\n");

  printf("\nOPTIONS   DESCRIPTIONS\n\n");
  printf("-p <str>    path for operator and fact file\n");
  printf("-o <str>    operator file name\n");
  printf("-f <str>    fact file name\n\n");

  printf("-e <num>    CNF encoding used (preset: %d)\n", gcmd_line.CNFencoding);
  printf("      0     Propositional CNF, expression-based\n");
  printf("      1     Propositional CNF, psi-based\n");
  printf("      2     Hybrid (mixed Boolean and numeric) CNF\n");
  printf("      3     Hybrid CNF with RPG-based value(t) clauses\n\n");

  printf("-s <num>    SAT solver used; only relevant for -e 0|1 (preset: %d)\n", gcmd_line.CNFsolver);
  printf("      0     Minisat\n");
  printf("      1     ZChaff\n\n");

  printf("-D          output problem data to file\n");
  printf("-T <int>    time out in seconds (preset: none)\n\n");

  printf("-O          keep numeric vars exclusively used in optimization criterion\n\n");

  if ( 0 ) {
    printf("-i <num>    run-time information level( preset: 1 )\n");
    printf("      0     only times\n");
    printf("      1     problem name, planning process infos\n");
    printf("    101     parsed problem data\n");
    printf("    102     cleaned up ADL problem\n");
    printf("    103     collected string tables\n");
    printf("    104     encoded domain\n");
    printf("    105     predicates inertia info\n");
    printf("    106     splitted initial state\n");
    printf("    107     domain with Wff s normalized\n");
    printf("    108     domain with NOT conds translated\n");
    printf("    109     splitted domain\n");
    printf("    110     cleaned up easy domain\n");
    printf("    111     unaries encoded easy domain\n");
    printf("    112     effects multiplied easy domain\n");
    printf("    113     inertia removed easy domain\n");
    printf("    114     easy action templates\n");
    printf("    115     cleaned up hard domain representation\n");
    printf("    116     mixed hard domain representation\n");
    printf("    117     final hard domain representation\n");
    printf("    118     reachability analysis results\n");
    printf("    119     facts selected as relevant\n");
    printf("    120     final domain and problem representations\n");
    printf("    121     collected constraints and psis\n\n");
    
    printf("-d <num>    switch on debugging\n");
    printf("-R          debug RPG\n");
    printf("-C          debug CNF\n\n");
  }

}



Bool process_command_line( int argc, char *argv[] )

{

  char option;

  gcmd_line.display_info = 1;
  gcmd_line.debug = 0;
  gcmd_line.CNFsolver = 0;
  gcmd_line.dRPG = FALSE;
  gcmd_line.dCNF = FALSE;
  gcmd_line.dHCNF = FALSE;
  gcmd_line.data = FALSE;
  gcmd_line.keep_optimization_vars = FALSE;
  gcmd_line.CNFencoding = 0;
  gcmd_line.T = -1;

  memset(gcmd_line.ops_file_name, 0, MAX_LENGTH);
  memset(gcmd_line.fct_file_name, 0, MAX_LENGTH);
  memset(gcmd_line.path, 0, MAX_LENGTH);
  memset(gcmd_line.mutex2ignore_file_name, 0, MAX_LENGTH);

  while ( --argc && ++argv ) {
    if ( *argv[0] != '-' || strlen(*argv) != 2 ) {
      return FALSE;
    }
    option = *++argv[0];
    switch ( option ) {
    case 'O':
      gcmd_line.keep_optimization_vars = TRUE;
      break;
    case 'R':
      gcmd_line.dRPG = TRUE;
      break;
    case 'C':
      gcmd_line.dCNF = TRUE;
      break;
    case 'H':
      gcmd_line.dHCNF = TRUE;
      break;
    case 'D':
      gcmd_line.data = TRUE;
      break;
    default:
      if ( --argc && ++argv ) {
	switch ( option ) {
	case 'a':
	  strncpy( only_keep_mutex_with, *argv, MAX_LENGTH );
	  break;
	case 'p':
	  strncpy( gcmd_line.path, *argv, MAX_LENGTH );
	  break;
	case 'o':
	  strncpy( gcmd_line.ops_file_name, *argv, MAX_LENGTH );
	  break;
	case 'f':
	  strncpy( gcmd_line.fct_file_name, *argv, MAX_LENGTH );
	  break;
	case 'm':
	  strncpy( gcmd_line.mutex2ignore_file_name, *argv, MAX_LENGTH );
	  break;
	case 'i':
	  sscanf( *argv, "%d", &gcmd_line.display_info );
	  break;
	case 'd':
	  sscanf( *argv, "%d", &gcmd_line.debug );
	  break;
	case 'e':
	  sscanf( *argv, "%d", &gcmd_line.CNFencoding );
	  break;
	case 's':
	  sscanf( *argv, "%d", &gcmd_line.CNFsolver );
	  break;
	case 'T':
	  sscanf( *argv, "%d", &gcmd_line.T );
	  break;
	default:
	  printf( "\nff: unknown option: %c entered\n\n", option );
	  return FALSE;
	}
      } else {
	return FALSE;
      }
    }
  }

  if ( gcmd_line.CNFencoding < 0 || gcmd_line.CNFencoding > 3 ) {
    printf("\nunknown CNF encoding -e");
    return FALSE;
  }

  if ( gcmd_line.CNFsolver < 0 || gcmd_line.CNFsolver > 3 ) {
    printf("\nunknown SAT solver -s");
    return FALSE;
  }

  return TRUE;

}

