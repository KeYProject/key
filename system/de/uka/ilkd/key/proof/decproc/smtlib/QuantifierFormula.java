// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.proof.decproc.DecisionProcedureSmtAufliaOp;

/** Represents a quantified formula as defined in the SMT-Lib specification, and specialized in
 * the (QF_)AUFLIA sublogic.<br>
 * Thereby the usual quantifiers FORALL and EXISTS are allowed operators. A 
 * <tt>QuantifierFormula</tt> takes one or more <tt>TermVariable</tt>s and an arbitrary 
 * <tt>Formula</tt> and quantifies the given <tt>TermVariable</tt>s in the given <tt>Formula</tt>
 * <p>
 * QuantifierFormula are immutable; their attribute values cannot be changed after they are
 * created.
 * 
 * @author akuwertz
 * @version 1.1,  10/06/2006  (Added support for many quantified variables)
 */

public class QuantifierFormula extends Formula {

    /* Additional fields */
    
    /* String constants for failures during Formula creation */ 
    private static final String creationFailureOpNull = "Operator is null!";
    private static final String creationFailureVarNull = "The array of term variables is null!";
    private static final String creationFailureNoQuantVars = 
        "The array of term variables is empty!";
    private static final String creationFailureVarContainsNull = 
        "The array of termvariables contains a null pointer!";
    private static final String creationFailureFormulaNull = "The formula is null!";
    private static final String creationFailureNoQuantifier = 
        "The given operator represents no quantifier!";
    private static final String creationFailureVarNotContained =
        "The variables to quantify must be contained in the specified formula!";
    private static final String creationFailureDuplicateVar = 
        "Duplicate term variable contained array quantVars!";
    
    
    
    /* Constructor */
    
    /** Creates a new <tt>QuantifierFormula</tt> out of a given array of <tt>TermVariable</tt>s 
     * and a given <tt>Formula</tt>.
     * <p>
     * The operator <tt>op</tt> must be one of the static quantifier operator <tt>String</tt>s 
     * defined in <tt>DecisionProcedureSmtAufliaOp</tt>.
     * 
     * @param op the quantifier used to quantify the variables in <tt>quantVars</tt>
     * @param quantVars the array of <tt>TermVariable</tt>s being quantified by <tt>op</tt>
     * @param formula the <tt>Formula</tt> in which the variables in <tt>quantVars</tt> should
     *                be quantified
     *                
     * @throws NullPointerException if <tt>op</tt>, <tt>quantVars</tt> or one of the contained 
     *                              <tt>TermVariables</tt>s, or <tt>formula</tt> is <tt>null</tt>
     * @throws IllegalArgumentException if <tt>op</tt> represents no quantifier in (QF_)AUFLIA 
     *                                  or if <tt>quantVars</tt> is empty or if at least one of
     *                                  the specified <tt>TermVariables</tt>s is not contained in
     *                                  <tt>formula</tt> or if duplicate <tt>TermVariable</tt>s
     *                                  are contained in <tt>quantVars</tt>
     *                                  
     * @see de.uka.ilkd.key.proof.decproc.DecisionProcedureSmtAufliaOp                                   
     */
    public QuantifierFormula( String op, TermVariable[] quantVars, Formula formula ) {
        super( op, new Formula[]{ formula }, quantVars );
        
        if ( op == null ) throw new NullPointerException( creationFailureOpNull );
        if ( quantVars == null ) throw new NullPointerException( creationFailureVarNull );
        if ( formula == null ) throw new NullPointerException( creationFailureFormulaNull );        
        
        if ( op != DecisionProcedureSmtAufliaOp.FORALL  &&
             op != DecisionProcedureSmtAufliaOp.EXISTS )
            throw new IllegalArgumentException( creationFailureNoQuantifier );
        
        if ( quantVars.length == 0 )
            throw new IllegalArgumentException( creationFailureNoQuantVars );
        Set containedVars = new HashSet();
        for( int i = 0; i < quantVars.length; i++ ) {
            if ( quantVars[i] == null ) 
                throw new NullPointerException( creationFailureVarContainsNull );
            if ( ! formula.containsTerm( quantVars[i] ) ) 
                throw new IllegalArgumentException( creationFailureVarNotContained );
            if ( ! containedVars.add( quantVars[i] ) )
                throw new IllegalArgumentException( creationFailureDuplicateVar );
        }    
    }
    
    
    
    // Public method implementation

    /** Returns true if this <tt>QuantifierFormula</tt> contains the <tt>Term</tt> <tt>term</tt>.
     * <p>
     * In a <tt>QuantifierFormula</tt> the quantified <tt>Term</tt> variables are not contained,
     * i.e. if this method is called with a quantified <tt>TermVariable</tt> as argument, it
     * will return <tt>false</tt>  
     * 
     * @param term the <tt>Term</tt> be checked for containment in this <tt>QuantifierFormula</tt>
     * @return true if this <tt>QuantifierFormula</tt> contains <tt>term</tt> and if <tt>term</tt>
     *              is unequal to its quantified variables
     */
    public boolean containsTerm( Term term ) {
        TermVariable[] quantVars = (TermVariable[]) getSubterms();
        for ( int i = 0; i < quantVars.length; i++ ) {
            if ( term.equals( quantVars[i] ) ) return false;
        }    
        return getSubformulae()[0].containsTerm( term );
    }
    
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Formula#equals(java.lang.Object)
     */
    public boolean equals( Object o ) {
        if ( o == this ) return true;
        if ( super.equals( o ) ) {
            return ( o instanceof QuantifierFormula );
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
        TermVariable[] quantVars = (TermVariable[]) getSubterms();
        String representation = "(" + getOp() + " ";
        for ( int i = 0; i < quantVars.length; i++ ) {
            representation += "(" + quantVars[i] + " " + quantVars[i].getSignature() + ") ";
        }    
        representation += getSubformulae()[0] + ")";
        return representation;
    }
    
    
    /* (non-Javadoc)
     * @see Formula#replaceFormVar(FormulaVariable, Formula)
     */
    public Formula replaceFormVar( FormulaVariable formVar, Formula replacement ) {
        if ( ! containsFormula( formVar ) ) return this;
        Formula replacedFormula = getSubformulae()[0].replaceFormVar( formVar, replacement );
        return new QuantifierFormula( getOp(), (TermVariable[]) getSubterms(), replacedFormula );
    }

    
    /* (non-Javadoc)
     * @see Formula#replaceTermVar(TermVariable, Term)
     */
    public Formula replaceTermVar( TermVariable termVar, Term replacement ) {
        if ( ! containsTerm( termVar ) ) return this;
        Formula replacedFormula = getSubformulae()[0].replaceTermVar( termVar, replacement );
        return new QuantifierFormula( getOp(), (TermVariable[]) getSubterms(), replacedFormula );
    }

}
