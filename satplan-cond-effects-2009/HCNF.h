


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
 * File: HCNF.h
 * Description: headers for RPG2HCNF
 *
 *
 * Author: Joerg Hoffmann 2006
 *
 *********************************************************************/ 








#ifndef _HCNF_H
#define _HCNF_H



void HCNF_initialize(RPGlayer *t, 
		     HCNF **cnfend,
		     int *numvars,
		     int *numclauses);
void HCNF_extend(RPGlayer *t, 
		 HCNF **cnfend,
		 int *numvars,
		 int *numclauses);
void HCNF_get_goal(RPGlayer *t, 
		   HCNF **cnfend, 
		   int *numclauses);
void HCNF_retract_goal(RPGlayer *t, 
		       HCNF **cnfend, 
		       int *numclauses);
void HCNF_print(RPGlayer *rpg,
		HCNF *cnf,
		int numvars,
		int numclauses);
void HCNF_print_exp(RPGlayer *rpg, ExpNode *exp);
void HCNF_print_infostring(RPGlayer *rpg, int CNFid);
void HCNF_statistics(RPGlayer *t, 
		     HCNF *cnf,
		     int numvars,
		     int numclauses);
void HCNF_output(RPGlayer *rpg,
		 HCNF *cnf,
		 int numvars,
		 int numclauses,
		 int bound);
void HCNF_output_exp(FILE *OUT, ExpNode *exp);



void HCNF_get_pre_con(RPGlayer *t, 
		      HCNF **cnfend, 
		      int *numclauses);
void HCNF_get_ea_ae(RPGlayer *t, 
		    HCNF **cnfend, 
		    int *numclauses);
void HCNF_get_eff(RPGlayer *t, 
		  HCNF **cnfend, 
		  int *numclauses);
void HCNF_get_frame(RPGlayer *t, 
		    HCNF **cnfend, 
		    int *numclauses);
void HCNF_get_aemutex(RPGlayer *t, 
		      HCNF **cnfend, 
		      int *numclauses);
void HCNF_get_eemutex(RPGlayer *t, 
		      HCNF **cnfend, 
		      int *numclauses);
void HCNF_get_tvalue(RPGlayer *t, 
		     HCNF **cnfend, 
		     int *numclauses);



ExpNode *HCNF_get_exp(RPGlayer *t, ExpNode *exp);



#endif /* _HCNF_H */
