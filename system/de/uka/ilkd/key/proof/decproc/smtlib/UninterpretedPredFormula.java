//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                    Universitaet Koblenz-Landau, Germany
//                    Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.decproc.smtlib;

import de.uka.ilkd.key.proof.decproc.DecisionProcedureSmtAufliaOp;

/** Represents an uninterpreted predicate formula as defined in the SMT-Lib specification, and
 * specialized in the (QF_)AUFLIA sublogic.
 * <p>
 * Uninterpreted predicates are identified by their top-level operator, i.e. their name. This name
 * therefore has to be a legal identifier in (QF_)AUFLIA, i.e. it must begin with a letter and may
 * consist only of letters, digits and the characters '.' , '_' and ''' (single quotation mark).
 * <br> Uninterpreted predicates are treated as non commutative predicates.
 * <p>
 * UninterpretedPredFormula are immutable; their attribute values cannot be changed after they
 * are created. 
 * 
 * @author akuwertz
 * @version 1.5,  12/11/2005  (Adjustments to superclass V1.5; further comments)
 */

public final class UninterpretedPredFormula extends Formula {

    /* Additional fields */
    
    /** The signature of this <tt>UninterpretedPredFormula</tt> */
    private final Signature signature;
    
    /* String constants for failures during Formula creation */
    private static final String creationFailureOpNull = "Operator is null!";
    private static final String creationFailureOpIllgId = "Operator is no legal identifier!";
    private static final String 
        creationFailureSubsContNull = "Subterm array contains a null pointer at position ";
    private static final String creationFailureSigNull = "The signature is null!";
    private static final String creationFailureArity = "Argument count does not match function arity!";
    private static final String creationFailureInterpreted = "Operator is an interpreted one!";
    
    
    
    /* Constructor */
    
    /** Creates a new <tt>UninterpretedPredFormula</tt> representing an uninterpreted predicate.
     * <p>
     * Every uninterpreted predicate is associated with a signature, which describes the number
     * and sorts of <tt>Term</tt> arguments of this <tt>UninterpretedPredFormula</tt>
     * <p>
     * To create an uninterpreted constant, <tt>subTerms</tt> can be either <tt>null</tt> or an
     * empty array; choosing <tt>null</tt> reduces the memory footprint through shared objects 
     * 
     * @param op the name assigned to the uninterpreted predicate to be represented
     * @param subTerms the array of argument <tt>Term</tt>s of this 
     *        <tt>UninterpretedPredFormula</tt>
     * @param sig the signature of this <tt>UninterpretedPredFormula</tt>
     * @throws NullPointerException if <tt>op</tt> or <tt>sig</tt> or one of the <tt>Term</tt>s
     *                              contained in <tt>subTerms</tt> is <tt>null</tt>
     * @throws IllegalArgumentException
     */
    public UninterpretedPredFormula( String op, Term[] subTerms, Signature sig ) {
        super( op, null, subTerms, true );
        if ( op == null ) throw new NullPointerException( creationFailureOpNull );
        if ( subTerms != null ) {
            for ( int i = 0; i < subTerms.length; i++ )
                if ( subTerms[i] == null ) 
                    throw new NullPointerException( creationFailureSubsContNull + i );
        }
        if ( sig == null ) throw new NullPointerException( creationFailureSigNull );

        // Check if op is syntactically correct
        if ( ! isLegalIdentifier( op ) ) 
                throw new IllegalArgumentException( creationFailureOpIllgId );    
        
        // Check if the operator op equals an interpreted operator. If yes, throw Exception.
        String[] interpretedOps = DecisionProcedureSmtAufliaOp.getAllSmtOperators();        
        for ( int i = 0; i < interpretedOps.length; i++ ) {            
            if ( interpretedOps[i].equals( op ) )
                throw new IllegalArgumentException( creationFailureInterpreted );
        }
        
        // Argument count and signature length must be equal
        if ( subTerms == null ) {
            if ( sig.getLength() != 0 ) throw new IllegalArgumentException( creationFailureArity ); 
        } else if ( subTerms.length != sig.getLength() ) {
            throw new IllegalArgumentException( creationFailureArity );
        }
        
        // Set signature 
        signature = sig;
    }    
    
    
    
    // Public method implementation
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Formula#equals(java.lang.Object)
     */
    public boolean equals( Object o ) {
        if ( o == this ) return true;
        if ( super.equals( o ) ) {
            // Uninterpreted predicates are treated non commutativ
            return ( o instanceof UninterpretedPredFormula );
        }
        return false;
    }
    
    
    /** Returns an int value representing the hash code of this <tt>UninterpretedPredFormula</tt>.
     * <p>
     * This hash code is calculated by combining the <tt>Formula</tt> hash code of this
     * <tt>UninterpretedPredFormula</tt> with the hash code of its <tt>Signature</tt>
     *  
     * @return the hash code of this <tt>UninterpretedPredFormula</tt>
     */
    public int hashCode() {
        return 37 * super.hashCode() + signature.hashCode();
    }

    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Formula#toString()
     */
    public String toString() {
        Term[] thisSubterms = getSubterms();
        if ( thisSubterms.length == 0 ) return getOp();
        String representation = "(" + getOp();
        for ( int i = 0; i < thisSubterms.length; i++ ) {
            representation += " " + thisSubterms[i].toString();
        }
        representation += ")";
        return representation;
    }
    
    
    /** Returns the signature of this <tt>UninterpretedPredFormula</tt>
     * 
     * @return the signature of this <tt>UninterpretedPredFormula</tt>
     */
    public Signature getSignature() {
        return signature;
    }


    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Formula#replaceFormVar(de.uka.ilkd.key.proof.decproc.smtlib.FormulaVariable, de.uka.ilkd.key.proof.decproc.smtlib.Formula)
     */
    public Formula replaceFormVar( FormulaVariable formVar, Formula replacement ) {
        if ( ! containsFormula( formVar ) ) return this;
        Term[] newSubterms = getSubterms();        
        for ( int i = 0; i < newSubterms.length; i++ ) {
            newSubterms[i] = newSubterms[i].replaceFormVarIteTerm( formVar, replacement );            
        }
        return new UninterpretedPredFormula( getOp() , newSubterms, signature );
    }


    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Formula#replaceTermVar(de.uka.ilkd.key.proof.decproc.smtlib.TermVariable, de.uka.ilkd.key.proof.decproc.smtlib.Term)
     */
    public Formula replaceTermVar( TermVariable termVar, Term replacement ) {
        if ( ! containsTerm( termVar ) ) return this;
        Term[] newSubterms = getSubterms();        
        for ( int i = 0; i < newSubterms.length; i++ ) {
            newSubterms[i] = newSubterms[i].replaceTermVar( termVar, replacement );            
        }
        return new UninterpretedPredFormula( getOp() , newSubterms, signature );
    }
}
