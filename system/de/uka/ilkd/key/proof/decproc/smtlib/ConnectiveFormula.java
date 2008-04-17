// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
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

/** Represents a complex formula composed of other formulae and a connective operator 
 * as defined in the SMT-Lib specification, and specialized in the (QF_)AUFLIA sublogic.
 * <p>
 * The different connective operators in QF_AULFIA are:
 *  - the logical AND
 *  - the logical OR
 *  - the logical XOR,
 *  - the logical implication IMP
 *  - the logical equivalence EQV
 *  - the logical NOT 
 *  - an 'if-then-else'-construct IFTHENELSE, for convenience 
 * <p>
 * ConnectiveFormulae are immutable; their attribute values cannot be changed after they are created.
 * 
 * @author akuwertz
 * @version 1.3,  12/12/2005  (Adjustments to superclass V1.5, further comments)
 */

public final class ConnectiveFormula extends Formula {

    /* Additional fields */
    
     /** A int used to cache the hash code of this <tt>ConnectiveFormula</tt> if it represents a
     * commutative connective symbol */
    private int cachedCommHashCode;
    
    /* String constants for failures during Formula creation */
    private static final String creationFailureOpNull = "Operator is null!";
    private static final String creationFailureSubsNull = "The subformulae array is null!";
    private static final String 
        creationFailureSubsContNull ="Subformulae array contains a null pointer at position ";
    private static final String creationFailureArity = "Argument count does not match function arity!";
    private static final String creationFailureNoConn= "Operator is not a connective symbol!";
    
    /* An array of all connective symbols */ 
    private static final String[]
        connectiveSymbols = { DecisionProcedureSmtAufliaOp.AND , DecisionProcedureSmtAufliaOp.OR ,
                              DecisionProcedureSmtAufliaOp.XOR , DecisionProcedureSmtAufliaOp.EQV , 
                              DecisionProcedureSmtAufliaOp.IMP , DecisionProcedureSmtAufliaOp.NOT ,
                              DecisionProcedureSmtAufliaOp.IFTHENELSE 
                            };
    
    
    
    
    /* Constructor */
    
    /** Creates a new <tt>ConnectiveFormula</tt> out of existing formulae and a connective operator.
     * <p>
     * The connective operator <tt>op</tt> must be one of the static connective operator
     * <tt>String</tt>s defined in <tt>DecisionProcedureSmtAufliaOp</tt>.<br>
     * Namely, these are AND, OR, XOR, EQV, IMP, NOT and IFTHENELSE.
     * <p>
     * All mentioned connectives but NOT and IFTHENELSE are of arity two. NOT is of arity one and
     * IFTHENELSE of arity three.<br>
     * The AND, OR, XOR and EQV connectives are treated as commutative operators.  
     * 
     * @param op the logical connective operator  
     * @param subForms the existing <tt>Formula</tt>e to be connected
     * @throws NullPointerException if <tt>op</tt>, <tt>subForms</tt> or one of the
     *                              <tt>Formula</tt>e contained in <tt>subForms</tt> is
     *                              <tt>null</tt>                              
     * @throws IllegalArgumentException if <tt>op</tt> is no connective symbol or if the number
     *                                  of given arguments doesn't match the expected arity
     * 
     * @see de.uka.ilkd.key.proof.decproc.DecisionProcedureSmtAufliaOp                                   
     */
    public ConnectiveFormula( String op, Formula[] subForms ) {
        super( op, subForms, null );
        if ( op == null ) throw new NullPointerException( creationFailureOpNull );
        if ( subForms == null ) throw new NullPointerException( creationFailureSubsNull );
        for ( int i = 0; i < subForms.length; i++ ) {
            if ( subForms[i] == null ) 
                throw new NullPointerException( creationFailureSubsContNull + i );
        }
        
        // Check if operator is a connective symbol
        boolean isConnective = false;
        for ( int i = 0; i < connectiveSymbols.length; i++ ) {
            if ( op == connectiveSymbols[i] ) {
                isConnective = true;
                i = connectiveSymbols.length;
            }
        }
        if ( !isConnective ) throw new IllegalArgumentException( creationFailureNoConn );
        
        // check arity for operator
        if ( op == DecisionProcedureSmtAufliaOp.IFTHENELSE ) {
            if ( subForms.length != 3 ) throw new IllegalArgumentException( creationFailureArity );
        } else if ( op == DecisionProcedureSmtAufliaOp.NOT ) {
            if ( subForms.length != 1 ) throw new IllegalArgumentException( creationFailureArity );    
        } else if ( subForms.length != 2 ) 
            throw new IllegalArgumentException( creationFailureArity );                                                                    
    }
    

    
    // Public method implementation
   
    /** Compares this <tt>ConnectiveFormula</tt> to the specified <tt>Object</tt> <tt>o</tt>. 
     * <p>
     * This <tt>ConnectiveFormula</tt> is considered equal to <tt>o</tt> if <tt>o</tt> is an
     * instance of <tt>ConnectiveFormula</tt> and has the same subformulae as this 
     * <tt>ConnectiveFormula</tt>.<br>
     * If the represented connective symbol is commutative, i.e. if this <tt>ConnetiveFormula</tt>
     * represents one of the connectives AND, OR, XOR or EQV, the order of arguments does
     * not matter for equality. For all other connective symbols in (QF_)AUFLIA, the order of 
     * arguments matters for equality.
     * 
     * @param o the <tt>Object</tt> to compare with 
     * @return true if this <tt>ConnectiveFormula</tt> is the same as the specified
     *         <tt>Object</tt>; otherwise false.
     */ 
    public boolean equals( Object o ) {
        if ( o == this ) return true;
        if ( o instanceof ConnectiveFormula ) {
            // Non commutative connectives, or commutative with same argument order
            if ( super.equals( o ) ) return true;
            // Commutative connectives
            ConnectiveFormula f = ( ConnectiveFormula ) o;
            String thisOp = getOp();
            if (  thisOp == DecisionProcedureSmtAufliaOp.AND 
                | thisOp == DecisionProcedureSmtAufliaOp.OR
                | thisOp == DecisionProcedureSmtAufliaOp.XOR
                | thisOp == DecisionProcedureSmtAufliaOp.EQV ) {
                Formula[] thisSubformulae = getSubformulae();
                Vector subformulae = toVector( thisSubformulae );
                Vector fSubformulae = toVector( f.getSubformulae() );
                if ( subformulae.containsAll( fSubformulae ) && 
                     fSubformulae.containsAll( subformulae ) ) { 
                    return true;
                }    
            }
        }
        return false;
    }

    
    /** Returns an int value representing the hash code of this <tt>ConnectiveFormula</tt>. 
     * <p>
     * The hash code for a <tt>ConnectiveFormula</tt> is calculated by combining the hash code of
     * its connective symbol with the hash codes of its subformulae.
     * <p>
     * If this <tt>ConnectiveFormula</tt> represents a commutative connective operator, i.e. if it
     * represents the AND, OR, XOR or EQV connective, the order of <tt>Formula</tt> arguments
     * doesn't not matter for the calculation, otherwise it does
     * 
     * @return the hash code of this <tt>PredicateFormula</tt>
     */ 
    public int hashCode() {
        String thisOp = getOp();
        // Non commutative connectives
        if ( thisOp == DecisionProcedureSmtAufliaOp.IMP || 
             thisOp == DecisionProcedureSmtAufliaOp.IFTHENELSE ) return super.hashCode();
        
        // Commutative connectives
        if ( cachedCommHashCode == 0) {
            Formula[] thisSubforms = getSubformulae();
            int result = 17;
            result = 37*result + thisOp.hashCode();
            int[] hashCodes = new int[ thisSubforms.length ];
            for ( int i = 0; i < thisSubforms.length; i++ ) {
                hashCodes[i] = thisSubforms[i].hashCode();                
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
        Formula[] thisSubformulae = getSubformulae();
        for ( int i = 0; i < thisSubformulae.length; i++ ) {
            representation += " " + thisSubformulae[i].toString();
        }
        representation += ")";
        return representation;
    }


    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Formula#replaceFormVar(de.uka.ilkd.key.proof.decproc.smtlib.FormulaVariable, de.uka.ilkd.key.proof.decproc.smtlib.Formula)
     */
    public Formula replaceFormVar( FormulaVariable formVar, Formula replacement ) {
        if ( ! containsFormula( formVar ) ) return this;
        Formula[] newSubformulae = getSubformulae();
        for ( int i = 0; i < newSubformulae.length; i++ ) {
            newSubformulae[i] = newSubformulae[i].replaceFormVar( formVar, replacement );
        }            
        return new ConnectiveFormula( getOp() , newSubformulae );
    }


    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Formula#replaceTermVar(de.uka.ilkd.key.proof.decproc.smtlib.TermVariable, de.uka.ilkd.key.proof.decproc.smtlib.Term)
     */
    public Formula replaceTermVar( TermVariable termVar, Term replacement ) {
        if ( ! containsTerm( termVar ) ) return this;
        Formula[] newSubformulae = getSubformulae();
        for ( int i = 0; i < newSubformulae.length; i++ ) {            
            newSubformulae[i] = newSubformulae[i].replaceTermVar( termVar, replacement );
        }            
        return new ConnectiveFormula( getOp(), newSubformulae );
    }
    
}
