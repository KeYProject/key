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

import de.uka.ilkd.key.logic.op.DecisionProcedureSmtAufliaOp;

/** Represents a formula variable as defined in the SMT-Lib specification, and specialized
 * in the (QF_)AUFLIA sublogic.
 * <p>
 * Thereby a formula variable is a variable, i.e. an identifier able to respresent an arbitrary
 * formula. An identifier is considered (syntactically) legal in (QF_)AUFLIA if it begins with a
 * letter and consists only of letters, digits and the characters '.' , '_' and ''' 
 * (single quotation mark).
 * <p>
 * FormulaVariable are immutable; their attribute values cannot be changed after they are created.   
 * 
 * @author akuwertz
 * @version 1.3,  12/09/2005  (Adjustments to superclass V1.5)
 */

public final class FormulaVariable extends Formula {

    /* Additional fields */
    
    /** String constant, representing the formula variable prefix in AUFLIA */
    private static final String formVarPrefix = "$";
    
    /* String constants for failures during Formula creation */    
    private static final String creationFailureIdNull = "Variable name is null!";
    private static final String creationFailureIdentIllg = "Variable name is no legal identifier!";
    private static final String creationFailureInterpreted = "Variable name equals an interpreted operator!";
    
    
    
    /* Constructor */
    
    /** Creates a <tt>FormulaVariable</tt>
     * 
     * @param formVar the identifier of the <tt>FormulaVariable</tt> to be represented
     * @throws NullPointerException if <tt>formVar</tt> is <tt>null</tt>
     * @throws IllegalArgumentException if <tt>formVar</tt> is no legal identifier or equals 
     *                                  an interpreted symbol in (QF_)AUFLIA
     */
    public FormulaVariable( String formVar ) {
        super( formVar , null , null );
        
        // Check if variable name formVar is syntactically correct
        if ( formVar == null ) throw new NullPointerException( creationFailureIdNull );
        if ( ! isLegalIdentifier( formVar) )  
                throw new IllegalArgumentException( creationFailureIdentIllg );
        
        
        // Check if formVar equals an interpreted operator in AUFLIA
        String[] interpretedOps = DecisionProcedureSmtAufliaOp.getAllSmtOperators();
        for( int i = 0; i < interpretedOps.length; i++ ) {
            if ( formVar.equals( interpretedOps[i] ) ) 
                throw new IllegalArgumentException( creationFailureInterpreted );
        }
    }
    
    
    
    // Public method implementation
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Formula#equals(java.lang.Object)
     */
    public boolean equals( Object o ) {
        if ( o == this ) return true;
        if ( super.equals( o ) ) {
            return ( o instanceof TruthValueFormula );
        }
        return false;
    }

    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Formula#hashCode()
     */
    public int hashCode() {
        return super.hashCode();
    }


    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Formula#toString()
     */
    public String toString() {
        return formVarPrefix + getOp();
    }


    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Formula#replaceFormVar(de.uka.ilkd.key.proof.decproc.smtlib.FormulaVariable, de.uka.ilkd.key.proof.decproc.smtlib.Formula)
     */
    public Formula replaceFormVar( FormulaVariable formVar, Formula replacement ) {
        return equals( formVar ) ? replacement : this;        
    }


    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Formula#replaceTermVar(de.uka.ilkd.key.proof.decproc.smtlib.TermVariable, de.uka.ilkd.key.proof.decproc.smtlib.Term)
     */
    public Formula replaceTermVar( TermVariable termVar, Term replacement ) {
        //  A FormulaVariable cannot contain any TermVariable
        return this;
    }
}
