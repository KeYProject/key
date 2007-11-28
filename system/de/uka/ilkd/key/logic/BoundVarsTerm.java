// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.Metavariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;

/** 
 * Used for OCL Simplification.
 * A BoundVarsTerm is an object that contains an Operator and several subterms.
 * It can also have a number of bound variables for each subterm.   
 * Instances should never be accessed via 
 * this interface, use the interface of the superclass Term and construct instances only via
 * a TermFactory instead.
 */
class BoundVarsTerm extends Term {

   /**
     * @supplierCardinality *
     * @supplierRole subterm
     * @link aggregation
     */
    private final ArrayOfTerm subTerm;

    /** variables that are bound in this term*/
    private final ArrayOfQuantifiableVariable[] boundVars;

    /** depth of the term */
    private final int depth;

    /** 
     * Creates an BoundVarsTerm with top operator op, some subterms,
     * zero or more bound variables for each subterm, and a sort.
     * @param op Operator at the top of the termstructure that starts
     * here.
     * @param subTerm An array containing subTerms (an array with length 0 if
     * there are no more subterms).
     * @param boundVars An array containing the bound variables.
     */
    public BoundVarsTerm(Operator op, Term[] subTerm, 
			 ArrayOfQuantifiableVariable[] boundVars) {
	super(op, op.sort(subTerm));
	this.subTerm = new ArrayOfTerm(subTerm);
	this.boundVars = boundVars;
	int max_depth = -1;
	for (int i = 0; i < subTerm.length; i++) {
	    if (subTerm[i].depth() > max_depth) {
		max_depth = subTerm[i].depth();	
	    }
	}
	depth = max_depth + 1;
	if (op instanceof QuantifiableVariable) {
	    freeVars = freeVars.add((QuantifiableVariable) op);
	} else if ( op instanceof Metavariable ) {
            metaVars = metaVars.add ( (Metavariable)op );
        }
	
	fillCaches();	
    }  

    /** @return arity of the term */
    public int arity() {
	return subTerm.size();
    }

    /**@return depth of the term */
    public int depth() {
	return depth;
    }

    /** the nr-th subterm */
    public Term sub(int nr) {
	return subTerm.getTerm(nr);
    }

    /** 
     * @return The array of variables bound for subterm n. 
     */
    public ArrayOfQuantifiableVariable varsBoundHere(int n) {
	if (n < 0 || n > boundVars.length-1) {
	    return EMPTY_VAR_LIST;
	} else {
	    return boundVars[n];
	}
    }

    // WATCHOUT: Woj: This is probably not necessary
    /**
     * returns a linearized textual representation of this term 
     */
    /*
    public String toString() {
	StringBuffer sb = new StringBuffer(op().name().toString());
	if (arity()==0) return sb.toString();
	sb.append("(");
	QuantifiableVariable qvar = null;
	for (int i=0;i<arity();i++) {
            if(varsBoundHere(i).size()==1){
	        sb.append("\\bind ");
		qvar = varsBoundHere(i).getQuantifiableVariable(0);
		if(qvar instanceof LogicVariable)
		  sb.append(((LogicVariable)qvar).sort()+" "+((LogicVariable)qvar).name());
		else
		  sb.append(qvar);
		sb.append("; ");
	    }else{
		for (int j=0; j<varsBoundHere(i).size(); j++) {
		    if (j==0) {
			sb.append("\\bind(");
		    }
		    qvar = varsBoundHere(i).getQuantifiableVariable(j);
		    if(qvar instanceof LogicVariable)
			sb.append(((LogicVariable)qvar).sort()+" "+((LogicVariable)qvar).name());
		    else
			sb.append(qvar);
		    if (j!=varsBoundHere(i).size()-1) {
		        sb.append("; ");
		    } else {
		        sb.append(")");
		    }
		}
            }
	    sb.append(sub(i));
	    if (i<arity()-1) {
		sb.append(",");
	    }
	}
	sb.append(")");
	return sb.toString();
    }
    */
}









