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

/** Represents a 'let'-construct formula as defined in the SMT-Lib specification,
 * and specialized in the (QF_)AUFLIA sublogic.<p>
 * Thereby a 'let'-construct consists of a formula f, a term variable termVar contained in f,
 * and a term t. It is semantically equivalent to the formula obtained by replacing every free
 * occurence of termVar in f by the term t.
 * <p>
 * LetFormula are immutable; their values cannot be changed after they are created
 * 
 * @author akuwertz
 * @version 1.4,  12/12/2005  (Adjustments to superclass V1.5; further comments)
 */

public class LetFormula extends Formula {

    /* Additional fields */
        
    /** The <tt>Formula</tt> to which this <tt>LetFormula</tt> is semantically equivant */
    private final Formula replacedFormula;
            
    /* String constants for failures during Formula creation */
    private static final String creationFailureTermVarNull = "The term variable is null!";
    private static final String creationFailureTermNull = "The replacement term t is null!";
    private static final String creationFailureFormulaNull = "The formula f is null!";
    private static final String 
        creationFailureVarNotCont = "The term variable must be contained in the formula f!";
    
    
    
    /* Constructor */
    
    /** Creates a new <tt>LetFormula</tt> using the 'let'-construct. 
     *  
     * @param tVar the <tt>TermVariable</tt> which is to be semantically replaced
     * @param t the <tt>Term</tt> which will be semantically inserted into f at every occurence of termVar
     * @param f the <tt>Formula</tt> in which termVar will be semantically replaced by t
     * @throws NullPointerException if one of the specified arguments is <tt>null</tt>
     * @throws IllegalArgumentException if <tt>termVar</tt> is not contained in <tt>f</tt>
     */   
    public LetFormula( TermVariable tVar, Term t, Formula f ) {                 
        super( DecisionProcedureSmtAufliaOp.LET, new Formula[]{ f }, new Term[]{ tVar, t } );
        
        // Check if a Constructor argument is null
        if ( tVar == null ) throw new NullPointerException( creationFailureTermVarNull );
        if ( t == null ) throw new NullPointerException( creationFailureTermNull );
        if ( f == null ) throw new NullPointerException( creationFailureFormulaNull );        
        
        // Check if termVar is contained in f
        if ( ! f.containsTerm ( tVar ) ) 
            throw new IllegalArgumentException( creationFailureVarNotCont );
        
        replacedFormula = f.replaceTermVar( tVar, t );
    }
    
    
    
    // Public method implementation
    
    /** Returns true if this <tt>LetFormula</tt> contains <tt>form</tt> as a subformula.
     * <p> 
     * In a 'let'-construct, the formula obtained by replacing every free occurence of its
     * <tt>TermVariable</tt> <tt>termVar</tt> in its <tt>Formula</tt> <tt>f</tt> by its
     * <tt>Term</tt> <tt>t</tt>, is checked for containing the specified <tt>Formula</tt>
     * <tt>form</tt>.     
     * 
     * @param form the <tt>Formula</tt> be checked for containment in this <tt>LetFormula</tt>
     * @return true if this <tt>LetFormula</tt> contains form
     */
    public boolean containsFormula( Formula form ) {                                      
        return replacedFormula.containsFormula( form );          
    }


    /** Returns true if this <tt>LetFormula</tt> contains the <tt>Term</tt> <tt>term</tt>.
     * <p>
     * In a 'let'-construct, the formula obtained by replacing every free occurence of its
     * <tt>TermVariable</tt> <tt>termVar</tt> in its <tt>Formula</tt> <tt>f</tt> by its
     * <tt>Term</tt> <tt>t</tt>, is checked for containing the specified <tt>Term</tt> term.
     * 
     * @param term the <tt>Term</tt> be checked for containment in this <tt>LetFormula</tt>
     * @return true if this <tt>LetFormula</tt> contains <tt>term</tt>
     */
    public boolean containsTerm( Term term ) {
        return replacedFormula.containsTerm( term );
    }

    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Formula#equals(java.lang.Object)
     */
    public boolean equals( Object o ) {
        if ( o == this ) return true;
        if ( super.equals( o ) ) {
            return ( o instanceof LetFormula );
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
        String representation = "(" + getOp();
        representation += " (" + getSubterms()[0] + " " + getSubterms()[1] + ") ";  
        representation += getSubformulae()[0] + ")";
        return representation;
    }

    
    /** Returns the term variable of this <tt>LetFormula</tt>
     * 
     * @return the term variable of this <tt>LetFormula</tt>
     */
    public TermVariable getTermVar() {
        return ( TermVariable ) getSubterms()[0];
    }
    
    
    /** Returns the replacement term t of this <tt>LetFormula</tt>
     * 
     * @return the term variable of this <tt>LetFormula</tt>
     */
    public Term getTermT() {
        return getSubterms()[1];
    }
    
    
    /** Returns the <tt>Formula</tt> f of this <tt>LetFormula</tt>
     * 
     * @return the <tt>Formula</tt> f of this <tt>LetFormula</tt>
     */
    public Formula getFormulaF() {
        return getSubformulae()[0];
    }


    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Formula#replaceFormVar(de.uka.ilkd.key.proof.decproc.smtlib.FormulaVariable, de.uka.ilkd.key.proof.decproc.smtlib.Formula)
     */
    public Formula replaceFormVar( FormulaVariable formVar, Formula replacement ) {        
        if ( ! containsFormula( formVar ) ) return this;
        return new LetFormula( getTermVar(), 
                               getTermT().replaceFormVarIteTerm( formVar , replacement ) ,
                               getFormulaF().replaceFormVar( formVar , replacement ) );
    }


    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Formula#replaceTermVar(de.uka.ilkd.key.proof.decproc.smtlib.TermVariable, de.uka.ilkd.key.proof.decproc.smtlib.Term)
     */
    public Formula replaceTermVar( TermVariable tVar, Term replacement ) {
        if ( ! containsTerm( tVar ) ) return this;
        return new LetFormula( getTermVar(), 
                               getTermT().replaceTermVar( tVar , replacement ) ,
                               tVar.equals( getTermVar() ) ? getFormulaF() :
                               getFormulaF().replaceTermVar( tVar , replacement ) );
    }
    
    
    /** Returns true if the specified <tt>Formula</tt> <tt>form</tt> equals the <tt>Formula</tt>
     * obtained from this <tt>LetFormula</tt> by replacing every free occurence of its
     * <tt>TermVariable</tt> <tt>termVar</tt> by its <tt>Term</tt> <tt>t</tt>.
     * 
     * @param form the <tt>Formula</tt> to be compared with the replaced <tt>Formula</tt> of
     *          this <tt>LetFormula</tt>
     * @return true if the specified <tt>Formula</tt> equals the replaced <tt>Formula</tt>
     *              of this <tt>LetFormula</tt>
     */
    public boolean equalsReplacedForm( Formula form ) {
        return replacedFormula.equals( form ); 
    }
    
    
    /** Returns the hash code of the <tt>Formula</tt> obtained from this <tt>LetFormula</tt>
     * by replacing every free occurence of its <tt>TermVariable</tt> <tt>termVar</tt> 
     * by its <tt>Term</tt> <tt>t</tt>.
     * 
     * @return the hash code of the replaced <tt>Formula</tt> of this <tt>LetFormula</tt>
     */
    public int hashCodeReplacedForm() {
        return replacedFormula.hashCode();
    }
}
