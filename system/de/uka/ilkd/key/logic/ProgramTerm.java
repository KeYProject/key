// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
/*
 * A ProgramTerm represents a term with a modality operator like
 * the diamond or box operator together with a JavaBlock. Instances
 * should never be accessed via this interface, use the interface of
 * the superclass Term and construct instances only via a TermFactory
 * instead. 
 */

class ProgramTerm extends Term {
    /** 
     * the program
     */
    private final JavaBlock javaBlock;

    /**  sub term */
    private final ArrayOfTerm subTerm; 

    /** caches depth */
    private int depth=-1;

    /** 
     * creates a diamond term, so there is an additional
     * parameter javaBlock 
     */
    ProgramTerm(Operator modality, 
		JavaBlock javaBlock, 
		Term subTerm) {
	this(modality, javaBlock, new Term[]{subTerm});
    }

    ProgramTerm(Operator op, 
		JavaBlock javaBlock, 
		Term[] subTerm) {
	super(op, op.sort(subTerm));
	this.subTerm=new ArrayOfTerm(subTerm);
	this.javaBlock=javaBlock;
    }

    /** @return n-th subterm (always the only one)*/    
    public Term sub(int n) {
	return subTerm.getTerm(n);
    }	
   
    /** @return arity of the quantifier term 1 as int */
    public int arity() {
	return subTerm.size();
    } 

    /**@return depth of the term */
    public int depth() {
	if(this.depth == -1) {
	    int localdepth = 0;
	    for(int i=0;i<subTerm.size();i++) {
		if(subTerm.getTerm(i).depth() > localdepth)
		    localdepth = subTerm.getTerm(i).depth();
	    }
	    this.depth = localdepth + 1;
	}
	return this.depth;
    }

    /** @return JavaBlock if term has diamond */
    public JavaBlock javaBlock() {
	return javaBlock;
    }
    
    /** @return an empty variable list */
    public ArrayOfQuantifiableVariable varsBoundHere(int n) {
	return EMPTY_VAR_LIST;
    }

    public String toString() {
	StringBuffer sb = new StringBuffer();
	if ( op() == Modality.DIA ) {
	    sb.append("\\<").append(javaBlock).append("\\> ");
	} else if ( op() == Modality.BOX ) {
	    sb.append("\\[").append(javaBlock).append("\\] ");
	} else {
	    //	    sb.append("???Some Strange Modality???").append(javaBlock);
	    sb.append("\\modality{"+op().name()).append("}").append(javaBlock).append("\\endmodality ");
	}
	for(int i=0; i<subTerm.size(); i++)
           sb.append("(").append(subTerm.getTerm(i)).append(")");

	return sb.toString();
    }

}
