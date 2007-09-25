// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.counterexample;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ConstructorFunction;
import de.uka.ilkd.key.logic.op.LogicVariable;

/**
 * Diese Klasse soll als Wrapper dienen fuer ibijas Termklassen.
 * es soll gleichzeitig darin gespeichert werden, ob der entsprechende
 * Term funktionsfrei ist.
 * @author Sonja Pieper
 * @version 1
 * @see AxiomCalculus
 */

class CExTerm{

    Term term;
    String opname,sorte;
    CExTerm[] params;
    
    private boolean fft;

  
    /*#AxiomCalculus lnkAxiomCalculus;*/

    CExTerm(Term t){
	term = t;
	sorte = (term.sort()).toString();
	opname  = (term.op()).toString();

	//the following builds the CExTerm structure recursivly
	//calculating the fft-property as a side effect.

	if(term.arity()>0){

	    //if a term is headed by a constructor and
	    //all subterms are function-free the term is function-free:

	    params = new CExTerm[term.arity()];	
	    boolean subs = true;
	    for(int i = 0;i<params.length;i++){
		params[i] = new CExTerm(term.sub(i));
		subs = subs && params[i].isFFT();
	    }
	    fft = subs && this.isConstr();
	}
	else {

	    //if the term is a constructor or a variable it is function-free:
	    
	    fft = this.isConstr() || this.isVar();
	}
    }


    /**
     * Generiere eine Liste der Parameter mit Reps fuer die nicht fft
     */
    public String paramsRep(){

	String paramsrep = new String("");
	if(params.length>0){
	    paramsrep = params[0].Rep();
	    for(int i=1;i<params.length;i++){
		paramsrep = paramsrep +","+params[i].Rep();
	    }
	}
	return paramsrep;
    }

    /**
     * wird bisher nur auf sich selbst aufgerufen als mit sich selbst als param
     */
    public String isRep(CExTerm res){
	return "is("+this.Rep()+","+res.opname+"(" + res.paramsRep() + "))";
    }

    /**
     * Nur fuer die optimierte Version der Ausgabe wichtig:
     * Daher getrennte von der eigentlichen Ausgabe.
     */
    public String interpretWith(CExTerm res){
	return "intpr("+opname+",tup"+params.length+
	    ( params.length>0 ? "("+this.paramsRep()+")" : "" ) /* keine klammer 0 params */
	    +","+res.Rep()+")";
    }

    /**
     * suchTerm fuer den platzhalter des termes
     */
    public String searchTerm(){
	return "search_"+sorte+"("+this.Rep()+")";
    }

    /**
     * Soll zurueckgeben ob fft oder nicht 
     */
    public boolean isFFT(){
	return fft;
    }

    public boolean isConstr(){
	return (term.op() instanceof ConstructorFunction); //@@@
    }

    public boolean isVar(){
	return (term.op() instanceof LogicVariable); //@@@
    }

     /**
      * Erstellung von Platzhaltern zu bestimmten Termen
      * ueberprueft ob ueberhaupt einer benoetigt wird anhand
      * der boolschen Variablen fft welche besagt ob 
      * es sich bei dem term um einen funktionsfreien Term handelt:
      */
     public String Rep(){
	 if (fft) { 
	     return this.toString(); 
	 }
	 return "val("+this.toString()+")";
     }

     public String toString(){

	 if (params.length == 0){ return opname; }

	 String s = new String();
	 for(int i=0;i<params.length;i++){
	     s = s + (i>0?",":"") + params[i].toString();
	 }
	 s = opname + "(" + s + ")";
	 return s;
     }

     /**
      * Hat ein FunctionTerm (z.B. ein konstruktor) keine Parameter
      * wird an dieser stelle ein array der laenge 0 zurueckgegeben.
      */
     public CExTerm[] getParams() {

	 if (params.length == 0) { 
	     System.out.println("Error: cannot getParams of non-FunctionTerm!");
	     return new CExTerm[0];
	 }
	 return params;
     }

}





