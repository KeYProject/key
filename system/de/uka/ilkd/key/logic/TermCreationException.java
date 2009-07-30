// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic;


import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.sort.*;


public class TermCreationException extends RuntimeException {

    private final String errorMessage;

    public TermCreationException(String errorMessage) {
	super(errorMessage);
	this.errorMessage = errorMessage;
    }

    public TermCreationException(Operator op, Term failed) {
	ArrayOfTerm subs = failed.subs();
	for (int i = 0, n = subs.size(); i < n; i++) {
	    Term sub = subs.getTerm(i);
	    assert sub == failed.subs().getTerm(i);
	}            

	errorMessage = 
	    "Building a term failed. Normally there is an arity mismatch " +
	    "or one of the subterms' sorts " +
	    "is not compatible (e.g. like the \'2\' in \"true & 2\")\n" +
	    "The top level operator was " + 
	    op + "(Sort: " + op.sort(subs) + ")" +
	    (op instanceof SortedOperator 
		    ? "; its expected arg sorts were:\n" + 
			    argsToString((SortedOperator)op) 
			    : "") + 
			    "\nThe subterms were:\n" + subsToString(subs);                       
    }

    public String getMessage() {          
	return errorMessage;
    }


    private String argsToString(SortedOperator f) {
	StringBuffer sb = new StringBuffer();
	for(int i = 0; i < f.arity(); i++) {
	    sb.append((i+1) + ".) ");
	    sb.append("sort: " + f.argSort(i) 
		      + (f.argSort(i) == null ? "" : ", sort hash: " + f.argSort(i).hashCode()) 
		      + "\n");
	}
	return sb.toString();
    }


    private String subsToString(ArrayOfTerm subs) {
	StringBuffer sb = new StringBuffer();
	for (int i = 0, n = subs.size(); i < n; i++) {
	    sb.append((i+1) + ".) ");
	    Term subi = subs.getTerm(i);
	    if(subi!=null){
		sb.append(subi);
		Sort subiSort = subi.sort();
		if(subiSort!=null){
		    sb.append("(sort: " + subi.sort()+
			    ", sort hash: "+ subi.sort().hashCode()+")\n");
		}else{
		    sb.append("(Unknown sort, \"null pointer\")");
		}
	    }else{
		sb.append(" !null! ");
	    }

	}
	return sb.toString();
    }


    public String toString() {
	return errorMessage;
    }
}
