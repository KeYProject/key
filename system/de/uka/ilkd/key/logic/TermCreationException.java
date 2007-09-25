// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
/*
 * Created on 01.02.2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;


/**
 * 
 */
public class TermCreationException extends RuntimeException {

        private String errorMessage;
        
        public TermCreationException(String errorMessage) {
            super(errorMessage);
            this.errorMessage = errorMessage;
        }
    
	public TermCreationException
            (Operator op, Term failed) {
            
            Term[] subs = new Term[failed.arity()];
            for (int i = 0; i<subs.length; i++) {
                subs[i] = failed.sub(i);
            }            
            
            errorMessage = 
                "Building a term failed. Normally there is an arity mismatch " +
                "or one of the subterms' sorts " +
                "is not compatible (e.g. like the \'2\' in \"true & 2\")\n" +
                "The top level operator was " + 
                op + "(Sort: " + op.sort(subs) + ")" +
                (op instanceof Function 
                 ? "; its expected arg sorts were:\n" + 
                	 argsToString((Function)op) 
                 : "\n") + 
                "The subterms were:\n" + subsToString(subs);                       
        }
     
	public String getMessage() {          
            return errorMessage;
	}
	
	
	private String argsToString(Function f) {
	    StringBuffer sb = new StringBuffer();
      	    for(int i = 0; i < f.arity(); i++) {
      		sb.append((i+1) + ".) ");
    	        sb.append("sort: " + f.argSort(i) + 
    	        	  ", sort hash: " + f.argSort(i).hashCode() + "\n");
      	    }
	    return sb.toString();
	}
	
	
        private String subsToString(Term[] subs) {
            StringBuffer sb = new StringBuffer();
            for (int i = 0; i<subs.length; i++) {
                sb.append((i+1) + ".) ");
                sb.append(subs[i]);
                sb.append("(sort: " + subs[i].sort()+
                          ", sort hash: "+ subs[i].sort().hashCode()+")\n");
        
            }
            return sb.toString();
        }
        
        
	public String toString() {
	    return errorMessage;
	}
}
