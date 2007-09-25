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

import java.util.Vector;

import de.uka.ilkd.key.logic.Axiom;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.ldt.ADT;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.Operator;

/**
 * This class generates the clauses for the axioms. It contains 
 * the complete Axiom Transformation algorithm as described in 
 * Wolfgang Ahrendt's PHD-Thesis 
 * @author Sonja Pieper
 * @version 0.1
 */
public class AxiomCalculus extends SortCalculus {

    private ADT adt;
    private Clauses axioms;

    
    /*#CExTerm lnkCExTerm;*/

    public AxiomCalculus(ADT a){
	super(a.getSorts());

	//@@@ visitor?variables
	adt = a;
	axioms = new Clauses();
        axioms.add(this.axiomClauses());
	this.all.add(axioms);
	
    }

    public Clauses getAxiomClauses(){
	return axioms;
    }

    /**
     * This method runs the loop so every axiom can be transformed with
     * <code>transAxiom(...)</code> and then added to the list of axiomclauses
     * @return the list of clauses with the transformed axioms
     */
    public Clauses axiomClauses(){

	Clauses cs = new Clauses();

	Vector axiomlist = adt.getAxioms();
	for(int axiomidx=0;axiomidx<axiomlist.size();axiomidx++){
	    cs.add(this.transAxiom((Axiom)axiomlist.elementAt(axiomidx)));
	}
	return cs;
    }

    /**
     * This is the start of the actual Transformation of the axioms.
     * @return The completely transformed axiom in the calculus clause format
     */
    public Clause transAxiom(Axiom axiom){

	String ante = new String(); 

	/* @@@ generate antecedent:
	  vars = axiom.freeVars();
	  while(vars.hasMoreElements()){
	     Term v = vars.next();
	     ante = ante + v.sort() + "("+ v.toString() +")";
	  }
	*/

	String cnsq = this.transDisj(axiom.getAxiomTerm());	

	//Axiom zu den Klauseln hinzufuegen:
	return new Clause(ante,cnsq);
    } 

    /**
     * Since an Axiom is a disjunktion of equalities or unequalities
     * one calls this funktion before being able to transform the equalities
     * which is done in the transLit function. A literal in this case
     * means an equality.
     *
     * @param term the first call gets the full axiom then it works down
     *             the disjunctions recursively.
     * @returns An mgtp-formatted string containing a disjunction of
     *          transformed equalities or inequalities.
     */
    public String transDisj(Term term){
	Operator operator = term.op();
    
	if ((operator == Op.EQV)||(operator == Op.NOT)) {
	    return this.transLit(term);
	}
	else if (operator == Op.OR) {
	    return this.transDisj(term.sub(0)) 
		+ ";" + this.transDisj(term.sub(1));
	}

	return "Error Wrong Top Level Operator";
    }


    /**
     * This method works with equalities mainly and calls on the
     * transformation methods for the two sides of the equality.
     *
     * @param lit A literal meaning either an equality or inequality
     * @return An mgtp formatted string which contains the transformed literal
     */
    public String transLit(Term lit){
	
	boolean eq = true;
	if(lit.op() == Op.NOT){
	    lit = lit.sub(0);
	    eq = false;
	}

	if(eq){
	    CExTerm[] t = { new CExTerm(lit.sub(0)), new CExTerm(lit.sub(1)) };	   
	    
	    if(CounterExample.config.optimize){

		//this is the optimized version of the transformation for equalities:
		if((t[0].isVar() || t[0].isConstr()) && 
		   (t[1].isVar() || t[1].isConstr())){
		    return "same("+t[0].Rep()+","+t[1].Rep()+")" + TransTermListe(t);
		}
		else if(t[0].isVar() || t[0].isConstr()){
		    return t[1].interpretWith(t[0]) + TransTermListe(t[1].getParams()) + TransTerm(t[0]);
		}
		else{
		    return t[0].interpretWith(t[1]) + TransTermListe(t[0].getParams()) + TransTerm(t[1]);
		}
	    }
	    else{//Unoptimized version of the transformation which is not as efficient
		return "same("+t[0].Rep()+","+t[1].Rep()+")"+ TransTermListe(t);
	    }
	    
	}
	else{ //different:
	    CExTerm[] t = { new CExTerm(lit.sub(0)), new CExTerm(lit.sub(1)) };
	    return "different("+t[0].Rep()+","+t[1].Rep()+")"+ TransTermListe(t);
	}

    }

    /**
     * ruft auf jedem CExTerm des Arrays CExTerm auf und baut eine Konjunktion zusammen
     * "," wird in der CExTerm eingefuegt!
     */

    public String TransTermListe(CExTerm[] termliste){
	String conj = new String();
	for(int i=0;i<termliste.length;i++){
	    conj = conj + TransTerm(termliste[i]);
	}
	return conj;
    }


    /**
     * Eigentliche Rekursion;
     * nachbedingung: nach ausfuehrung fuer Transterm muss bekannt
     * sein ob ein ffterm nun fft ist oder nicht!!!!
     */
    public String TransTerm(CExTerm term){

	if (term.isFFT()) { 
	    return ""; 
	}
	else if (term.isConstr()) {
	    return ",\n\t\t" + term.isRep(term) + TransTermListe(term.getParams());
	}
	else {
	    return ",\n\t\t" + term.interpretWith(term) 
		+","+ term.searchTerm() + TransTermListe(term.getParams());
	}
    }

}
