// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//            Universitaet Koblenz-Landau, Germany
//            Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.decproc.smtlib;

import de.uka.ilkd.key.proof.decproc.DecisionProcedureSmtAufliaOp;

/** Represents a term variable as defined in the SMT-Lib specification, and specialized
 * in the (QF_)AUFLIA sublogic. Thereby a term variable is a variable (identifier) that
 * respresent an arbitrary term. The identifier is a String, starting with a letter and
 * containing only letters, digits, "_", "'" and "."
 * <p>
 * TermsVariables are immutable; their attribute values cannot be changed once they are 
 * created.
 * 
 * @author akuwertz
 * @version 1.5,  09/29/2006  (Added signatures to term variables)                             
 */

public final class TermVariable extends Term {

    /* Additional fields */
            
    /** String constant, representing the term variable prefix in AUFLIA */
    private static final String termVarPrefix = "?";
    
    /** A <tt>Signature</tt> representing the sort of this <tt>TermVariable</tt> */
    private final Signature sort;
    
    /** A int to cache the hash code for this <tt>TermVariable</tt> */
    private int cachedHashCode;
    
    /* String constants for failures during Term creation */
    private static final String creationFailureIdNull = "Variable name is null!";
    private static final String creationFailureIdIllg = "Variable name is no legal identifier!!";
    private static final String creationFailureInterpreted = 
        "Variable name equals an interpreted operator!";
    private static final String creationFailureSigNull = "The signature is null!";
    private static final String creationFailureWrongSig = 
        "The signature must contain exactly one sort";
    
    
    
    /* Constructor */
    
    /** Creates a new <tt>TermVariable</tt>
     *  
     * @param varName the identifier of the <tt>Term</tt> variable to be represented
     * @param sig the <tt>Signature</tt> denoting the sort of this <tt>Term</tt> variable
     * @throws NullPointerException if <tt>varName</tt> is <tt>null</tt>
     * @throws IllegalArgumentException if <tt>varName</tt> contains an illegal character
     *                                  or equals an interpreted symbol in (QF_)AUFLIA 
     */
    public TermVariable( String varName, Signature sig ) {
        super( varName , new Term[0] , null , null );
        
        // Check if varName is syntactically correct
        if ( varName == null ) throw new NullPointerException( creationFailureIdNull );
        if ( ! isLegalIdentifier( varName ) )
                throw new IllegalArgumentException( creationFailureIdIllg );            

        // Check if varName equals an interpreted operator in AUFLIA
        String[] interpretedOps = DecisionProcedureSmtAufliaOp.getAllSmtOperators();
        for( int i = 0; i < interpretedOps.length; i++ ) {
            if ( varName.equals( interpretedOps[i] ) ) 
                throw new IllegalArgumentException( creationFailureInterpreted );
        }
        
        if ( sig == null ) throw new NullPointerException( creationFailureSigNull );
        if ( sig.getLength() != 1 ) throw new IllegalArgumentException( creationFailureWrongSig );
        sort = sig;
    }
    
    
        
    // Public method implementation
     
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Term#equals(de.uka.ilkd.key.proof.decproc.smtlib.Term)
     */
    public boolean equals( Object o ) {
        if ( this == o ) return true;
        if ( super.equals( o ) ) {
            if ( o instanceof TermVariable ) 
                return sort.equals( ( (TermVariable) o).getSignature() );
        }
        return false;
    }
        
    
    /** Returns an int value representing the hash code of this <tt>TermVariable</tt>.
     * <p>
     * This hash code is calculated by combining the <tt>Term</tt> hash code of this 
     * <tt>TermVariable</tt> with the hash code of its <tt>Signature</tt>
     *  
     * @return the hash code of this <tt>TermVariable</tt>
     */
    public int hashCode() {
        if ( cachedHashCode == 0 ) {
            cachedHashCode = 37*super.hashCode() + sort.hashCode();
        }
        return cachedHashCode;
    }


    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Term#toString()
     */
    public String toString() {
        return termVarPrefix + getFunction();        
    }
    

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Term#replaceTermVar(de.uka.ilkd.key.proof.decproc.smtlib.TermVariable, de.uka.ilkd.key.proof.decproc.smtlib.Term)
     */
    public Term replaceTermVar( TermVariable termVar, Term replacement ) {
        // If this TermVariable is to be replaced, do it, otherwise let it unchanged
        return equals( termVar ) ? replacement : this;
    }


    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Term#replaceFormVarIteTerm(de.uka.ilkd.key.proof.decproc.smtlib.FormulaVariable, de.uka.ilkd.key.proof.decproc.smtlib.Formula)
     */
    public Term replaceFormVarIteTerm( FormulaVariable formVar, Formula replacement ) {
        return this;
    }
    
    
    /** Returns the signature (sort) of this <tt>TermVariable</tt>
     * 
     * @return the signature of this <tt>TermVariable</tt>
     */
    public Signature getSignature() {
        return sort;
    }
}
