


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
 * File: RPGvaluetuples.h
 * Description: headers for fully fledged numeric RPG.
 *
 *
 * Author: Joerg Hoffmann 2006
 *
 *********************************************************************/ 








#ifndef _RPG_VALUETUPLES_H
#define _RPG_VALUETUPLES_H



void RPG_get_valuetuples(RPGlayer *t,
			 int *psi,
			 int num_psi);
void RPG_get_valuetuples_exp(RPGlayer *t,
			     int id,
			     ExpNode *exp);



void RPG_get_VT_and_V(int recd, 
		      RPGlayer *t,
		      RPGvaluetuple *vt,
		      ExpNode *exp);



#endif /* _RPG_VALUETUPLES_H */
