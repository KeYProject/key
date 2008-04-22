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

import java.util.Vector;

import de.uka.ilkd.key.proof.decproc.DecisionProcedureSmtAufliaOp;

/** Represents a predicate formula as defined in the SMT-Lib specification, and specialized
 * in the (QF_)AUFLIA sublogic. 
 * <p>
 * Thereby only the predicates '=', '<=', '<', '>=' and '>' are supported in (QF_)AUFLIA; for
 * convenience there's also the 'distinct'-construct.
 * <p>
 * PredicateFormula are immutable; their attribute values cannot be changed after they are created.  
 *  
 * @author akuwertz
 * @version 1.3,  12/09/2005  (Adjustments to superclass V1.5, further comments)
 */

public final class PredicateFormula extends Formula {

    /* Additional fields */
    
    /** A int used to cache the hash code of this <tt>PredicateFormula</tt> if it represents a
     * commutative function */
    private int cachedCommHashCode;
    
    /* String constants for failures during Formula creation */
    private static final String creationFailureOpNull = "Operator is null!";
    private static final String creationFailureSubsNull = "Subterm array is null!";
    private static final String 
        creationFailureSubsContNull = "Subterm array contains a null pointer at position ";
    private static final String creationFailureArity = "Argument count does not match function arity!";
    private static final String creationFailureNoPred= "Operator is not a predicate symbol!";
    
    
    /* An array of all interpreted predicate symbols */
    private static final String[] 
        predicateSymbols = { DecisionProcedureSmtAufliaOp.GEQ , DecisionProcedureSmtAufliaOp.GT ,
                             DecisionProcedureSmtAufliaOp.LEQ , DecisionProcedureSmtAufliaOp.LT , 
                             DecisionProcedureSmtAufliaOp.EQUALS, DecisionProcedureSmtAufliaOp.DISTINCT 
                           };
     
    
    
    /* Constructor */
    
    /** Creates a new <tt>PredicateFormula</tt> representing an interpreted predicate.
     * <p>
     * The predicate symbol <tt>op</tt> must be one of the static <tt>String</tt>s defined in
     * <tt>DecisionProcedureSmtAufliaOp</tt>. Namely, these are EQUALS, GEQ, GT, LEQ, LT and DISTINCT.
     * <p>
     * All mentioned predicates but the DISTINCT predicate are of arity two. For DISTINCT, any
     * integer value greater than one is allowed as number of argument <tt>Term</tt>s.<br>
     * Only the DISTINCT and the EQUALS predicate are commutative 
     * 
     * @param op the predicate symbol to be represented
     * @param subTerms the array of <tt>Term</tt> arguments of this <tt>PredicateFormula</tt>
     * @throws NullPointerException if <tt>op</tt> or one of the <tt>Term</tt>s contained
     *                              in <tt>subTerms</tt> is <tt>null</tt>
     * @throws IllegalArgumentException if <tt>op</tt> represents no interpreted predicate in 
     *                                  (QF_)AUFLIA or if the specified argument <tt>Term</tt>s
     *                                  don't match the predicate arity
     *
     * @see de.uka.ilkd.key.proof.decproc.DecisionProcedureSmtAufliaOp                                   
     */
    public PredicateFormula( String op, Term[] subTerms ) {
        super( op, null, subTerms );
        if ( op == null ) throw new NullPointerException( creationFailureOpNull );
        if ( subTerms == null ) throw new NullPointerException( creationFailureSubsNull );
        for ( int i = 0; i < subTerms.length; i++ ) {
            if ( subTerms[i] == null ) 
                throw new NullPointerException( creationFailureSubsContNull + i);
        }
        
        // Check if operator is a predicate symbol
        boolean isPredicate = false;
        for (int i = 0 ; i < predicateSymbols.length; i++ ) {
            if ( op == predicateSymbols[i] ) {
                isPredicate = true;
                i = predicateSymbols.length;
            }
        }    
        if ( !isPredicate ) throw new IllegalArgumentException( creationFailureNoPred );

        // Check arity
        if ( ( op != DecisionProcedureSmtAufliaOp.DISTINCT  &  subTerms.length != 2 )
           | ( op == DecisionProcedureSmtAufliaOp.DISTINCT  &  subTerms.length < 2 ) )   
            throw new IllegalArgumentException( creationFailureArity );        
    }
    
    
    
    // Public method implementation
    
    /**
     * Compares this <tt>Formula</tt> to the specified <tt>Object</tt> <tt>o</tt>.
     * <p>
     * This <tt>PredicateFormula</tt> is considered equal to <tt>o</tt> if <tt>o</tt> is an
     * instance of <tt>PredicateFormula</tt> and has the same subterms as this
     * <tt>PredicateFormula</tt>.<br>
     * If the represented predicate is commutative, i.e. if this <tt>PredicateFormula</tt>
     * represents the EQU or DISTINCT predicate, the order of arguments does not matter for
     * equality. For all other interpreted predicates in (QF_)AUFLIA, the order of arguments matters
     * for equality.
     * 
     * @param o
     *            the <tt>Object</tt> to compare with
     * @return true if this <tt>PredicateFormula</tt> is the same as the specified <tt>Object</tt>;
     *         otherwise false.
     */ 
    public boolean equals( Object o ) {
        if ( o == this ) return true;
        if ( o instanceof PredicateFormula ) {
            // Non commutative predicates, and commutative with same argument order
            if ( super.equals( o ) ) return true;
            // Commutative predicates (argument order does not matter)    
            PredicateFormula f = ( PredicateFormula ) o;
            String thisOp = getOp();
            if (  thisOp == DecisionProcedureSmtAufliaOp.DISTINCT 
                | thisOp == DecisionProcedureSmtAufliaOp.EQUALS ) {
                Vector subterms = toVector( getSubterms() );
                Vector fSubterms = toVector( f.getSubterms() );
                if (   subterms.containsAll( fSubterms )  &&  fSubterms.containsAll( subterms ) )
                    return true;
            }
        }    
        return false;    
    }

    
    /** Returns an int value representing the hash code of this <tt>PredicateFormula</tt>. 
     * <p>
     * The hash code for a <tt>PredicateFormula</tt> is calculated by combining the hash code of
     * its predicate symbol (operator) with the hash codes of its <tt>Term</tt> arguments.
     * <p>
     * If this <tt>PredicateFormula</tt> represents a commutative predicate, i.e. if it represents
     * the EQU or DISTINCT predicate, the order of <tt>Term</tt> arguments doesn't not matter for 
     * the calculation, otherwise it does
     * 
     * @return the hash code of this <tt>PredicateFormula</tt>
     */  
    public int hashCode() {
        String thisOp = getOp();
        // Non commutative predicates
        if ( thisOp != DecisionProcedureSmtAufliaOp.EQUALS  &&  
             thisOp != DecisionProcedureSmtAufliaOp.DISTINCT ) {
            return super.hashCode();
        }
        // Commutative predicates
        if ( cachedCommHashCode == 0 ) { 
            Term[] thisSubterms = getSubterms();
            int result = 17;
            result = 37*result + thisOp.hashCode();
            int[] hashCodes = new int[ thisSubterms.length ];
            for ( int i = 0; i < thisSubterms.length; i++ ) {
                hashCodes[i] = thisSubterms[i].hashCode();                
            }
            // Use the sum and the product of calculated argument hashes 
            int sum = 0;
            int product = 1;
            for ( int i = 0; i < hashCodes.length; i++ ) {
                sum += hashCodes[i];
                product *= hashCodes[i];
            }
            result = 37*result + sum;
            result = 37*result + product;
            cachedCommHashCode = result;
        }
        return cachedCommHashCode;
    }
    
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Formula#toString()
     */
    public String toString() {
        String representation = "(" + getOp();
        Term[] thisSubterms = getSubterms();
        for ( int i = 0; i < thisSubterms.length; i++ ) {
            representation += " " + thisSubterms[i].toString();
        }
        representation += ")";
        return representation;
    }


    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Formula#replaceFormVar(de.uka.ilkd.key.proof.decproc.smtlib.FormulaVariable, de.uka.ilkd.key.proof.decproc.smtlib.Formula)
     */
    public Formula replaceFormVar( FormulaVariable formVar, Formula replacement ) {
        // A PredicateFormula cannot contain any FormulaVariable, but the contained terms
        // could be IteTerms containing a Formula
        if ( ! containsFormula( formVar ) ) return this;
        Term[] newSubterms = getSubterms();        
        for ( int i = 0; i < newSubterms.length; i++ ) {
            newSubterms[i] = newSubterms[i].replaceFormVarIteTerm( formVar, replacement );
        }    
        return new PredicateFormula( getOp() , newSubterms );
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
        return new PredicateFormula( getOp() , newSubterms );
    }
}
