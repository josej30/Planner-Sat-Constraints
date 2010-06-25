


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
 * File: CNF.h
 * Description: headers for RPG2CNF
 *
 *
 * Author: Joerg Hoffmann 2006
 *
 *********************************************************************/ 








#ifndef _CNF_H
#define _CNF_H



void CNF_initialize(RPGlayer *t, 
		    CNF **cnfend,
		    int *numvars,
		    int *numclauses);
void CNF_extend(RPGlayer *t, 
		CNF **cnfend,
		int *numvars,
		int *numclauses);
void CNF_get_goal(RPGlayer *t, 
		  CNF **cnfend, 
		  int *numclauses);
void CNF_retract_goal(RPGlayer *t, 
		      CNF **cnfend, 
		      int *numclauses);
void CNF_print(RPGlayer *rpg,
	       CNF *cnf,
	       int numvars,
	       int numclauses);
void CNF_print_infostring(RPGlayer *rpg, int CNFid);
void CNF_output(CNF *cnf,
		int numvars,
		int numclauses,
		int bound);
void CNF_statistics(RPGlayer *t, 
		    CNF *cnf,
		    int numvars,
		    int numclauses);
int CNF_output_plan(FILE *SATRES,
		    RPGlayer *rpg,
		    int numvars);



void CNF_get_constraint_constraintvt(RPGlayer *t, 
				     CNF **cnfend, 
				     int *numclauses);
void CNF_get_psi_psivt(RPGlayer *t, 
		       CNF **cnfend, 
		       int *numclauses);
void CNF_get_pre_con(RPGlayer *t, 
		     CNF **cnfend, 
		     int *numclauses);
void CNF_get_ea_ae(RPGlayer *t, 
		   CNF **cnfend, 
		   int *numclauses);
void CNF_get_eff(RPGlayer *t, 
		 CNF **cnfend, 
		 int  *numclauses);
void CNF_get_frame(RPGlayer *t, 
		   CNF **cnfend, 
		   int *numclauses);
void CNF_get_vmutex(RPGlayer *t, 
		    CNF **cnfend, 
		    int *numclauses);
void CNF_get_aemutex(RPGlayer *t, 
		     CNF **cnfend, 
		     int *numclauses);
void CNF_get_eemutex(RPGlayer *t, 
		     CNF **cnfend, 
		     int *numclauses);



#endif /* _CNF_H */
