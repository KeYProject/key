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

import de.uka.ilkd.key.proof.decproc.DecisionProcedureSmtAufliaOp;

/** Represents a 'flet'-construct formula as defined in the SMT-Lib specification,
 * and specialized in the (QF_)AUFLIA sublogic.
 * <p>
 * Thereby a 'flet'-construct consists of a formula f1, a formula variable fVar and an arbitrary
 * formula f0, and is semantically equivalent to the Formula obtained by replacing every free 
 * occurence of formVar in f1 by the Formula f0.
 * <p>
 * FletFormula are immutable; their values cannot be changed after they are created
 * 
 * @author akuwertz
 * @version 1.4,  12/12/2005  (Adjustments to superclass V1.5; further comments)
 */

public class FletFormula extends Formula {

    /* Additional fields */
    
    /** The <tt>Formula</tt> to which this <tt>FletFormula</tt> is semantically equivant */
    private final Formula replacedFormula;
    
    /* String constants for failures during Formula creation */
    private static final String creationFailureFormVarNull = "The formula variable is null!";
    private static final String creationFailureFormulaf0Null = "The replacement formula f0 is null!";
    private static final String creationFailureFormulaf1Null = "The formula f1 is null!";
    private static final String 
        creationFailureVarNotCont = "The formula variable must be contained in the formula f1!";
    
    
    
    /* Constructor */
    
    /** Creates a new <tt>FletFormula</tt> using the 'flet'-construct.   
     *
     * @param fVar the <tt>FormulaVariable</tt> occuring in <tt>f1</tt> which is to be semantically replaced
     * @param f0 the <tt>Formula</tt> which will semantically replace fVar in <tt>f1</tt>
     * @param f1 the <tt>Formula</tt> in which fVar will be semantically replaced by <tt>f0</tt>
     * @throws NullPointerException if one of the arguments is <tt>null</tt>
     * @throws IllegalArgumentException if <tt>fVar</tt> is not contained in <tt>f1</tt>
     */   
    public FletFormula( FormulaVariable fVar, Formula f0, Formula f1 ) {
        super( DecisionProcedureSmtAufliaOp.FLET, new Formula[]{ fVar, f0, f1 }, null );

        // Check if a Constructor argument is null
        if ( fVar == null ) throw new NullPointerException( creationFailureFormVarNull );
        if ( f0 == null ) throw new NullPointerException( creationFailureFormulaf0Null );
        if ( f1 == null ) throw new NullPointerException( creationFailureFormulaf1Null );
        
        // Check if fVar is contained in f1        
        if ( !f1.containsFormula ( fVar ) ) 
            throw new IllegalArgumentException( creationFailureVarNotCont );
        
        replacedFormula = f1.replaceFormVar( fVar , f0 );
    }
    
    
    // Public method implementation
    
    /** Returns true if this <tt>FletFormula</tt> contains the <tt>Formula</tt> <tt>f</tt>.
     * <p> 
     * In a 'flet'-construct, the formula obtained by replacing every free occurence of its
     * <tt>FormulaVariable</tt> <tt>fVar<tt> in its <tt>Formula</tt> <tt>f1</tt> by its
     * <tt>Formula</tt> <tt>f0</tt>, is checked for containing the specified <tt>Formula</tt>
     * <tt>f</tt>.     
     * 
     * @param f the <tt>Formula</tt> be checked for containment in this <tt>FletFormula</tt>
     * @return true if this <tt>FletFormula</tt> contains <tt>f</tt>
     */
    public boolean containsFormula( Formula f ) {
        return replacedFormula.containsFormula( f );
    }

    
    /** Returns true if this <tt>FletFormula</tt> contains the <tt>Term</tt> <tt>t</tt>. 
     * In a 'flet'-construct, the formula obtained by replacing every free occurence of its
     * <tt>FormulaVariable</tt> <tt>fVar</tt> in its <tt>Formula</tt> <tt>f1</tt> by its 
     * <tt>Formula</tt> <tt>f0</tt>, is checked for containing the specified <tt>Term</tt>
     * <tt>t</tt>.     
     * 
     * @param t the <tt>Term</tt> be checked for containment in this <tt>FletFormula</tt>
     * @return true if this <tt>FletFormula</tt> contains <tt>t</tt>
     */
    public boolean containsTerm( Term t ) {
        return replacedFormula.containsTerm( t );             
    }

    
    /* (non-Javadoc)
     * @see Formula#equals(java.lang.Object)
     */
    public boolean equals( Object o ) {
        if ( o == this ) return true;
        if ( super.equals( o ) ) {
            return ( o instanceof LetFormula );
        }
        return false;
    }
    
    
    /* (non-Javadoc)
     * @see Formula#hashCode()
     */
    public int hashCode() {
        return super.hashCode();
    }


    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Formula#toString()
     */
    public String toString() {
        String representation = "(" + getOp();
        representation += " (" + getSubformulae()[0] + " " + getSubformulae()[1] + ") ";
        representation += getSubformulae()[2] + ")";
        return representation;
    }
    

    /** Returns the formula variable of this <tt>FletFormula</tt>
     * 
     * @return the <tt>FormulaVariable</tt> fVar of this <tt>FletFormula</tt>
     */
    public FormulaVariable getFormVar() {
        return ( FormulaVariable ) getSubformulae()[0];
    }
    
    
    /** Returns the <tt>Formula</tt> <tt>f0</tt> of this <tt>FletFormula</tt>
     *  
     * @return the <tt>Formula</tt> <tt>f0</tt> of this <tt>FletFormula</tt>
     */
    public Formula getFormulaF0() {
        return getSubformulae()[1];
    }
    
    
    /** Returns the <tt>Formula</tt> <tt>f1</tt> of this <tt>FletFormula</tt>
     *  
     * @return the <tt>Formula</tt> <tt>f1</tt> of this <tt>FletFormula</tt>
     */
    public Formula getFormulaF1() {
        return getSubformulae()[2];
    }


    /* (non-Javadoc)
     * @see Formula#replaceFormVar(FormulaVariable, Formula)
     */
    public Formula replaceFormVar(FormulaVariable fVar, Formula replacement) {
        if ( ! containsFormula( fVar ) )
            return this;
        return new FletFormula( getFormVar(), 
                                getFormulaF0().replaceFormVar( fVar , replacement ) ,
                                fVar.equals( getFormVar() ) ? getFormulaF1() :
                                getFormulaF1().replaceFormVar( fVar , replacement ) );
    }


    /* (non-Javadoc)
     * @see Formula#replaceTermVar(TermVariable, Term)
     */
    public Formula replaceTermVar(TermVariable termVar, Term replacement) {        
         if ( ! containsTerm( termVar ) ) return this;
        return new FletFormula( getFormVar(), 
                                getFormulaF0().replaceTermVar( termVar , replacement ) ,
                                getFormulaF1().replaceTermVar( termVar , replacement ) );
    }
    
    
    /** Returns true if the specified <tt>Formula</tt> <tt>f</tt> equals the <tt>Formula</tt> obtained
    * from this <tt>FletFormula</tt> by replacing free occurence of its <tt>FormulaVariable</tt>
    * <tt>fVar</tt> in its <tt>Formula</tt> <tt>f1</tt> by its <tt>Formula</tt> <tt>f0</tt>.
    * 
    * @param f the <tt>Formula</tt> to be compared with the replaced <tt>Formula</tt> of
    *          this <tt>FletFormula</tt>
    * @return true if the specified <tt>Formula</tt> equals the replaced <tt>Formula</tt>
    *              of this <tt>FletFormula</tt>
    */
   public boolean equalsReplacedForm( Formula f ) {
       return replacedFormula.equals( f ); 
   }
   
   
   /** Returns the hash code of the <tt>Formula</tt> obtained from this <tt>FletFormula</tt> by
    * replacing free occurence of its <tt>FormulaVariable</tt> <tt>fVar</tt> in its <tt>Formula</tt>
    * <tt>f1</tt> by its <tt>Formula</tt> <tt>f0</tt>.
    * 
    * @return the hash code of the replaced <tt>Formula</tt> of this <tt>FletFormula</tt>
    */
    public int hashCodeReplacedForm() {
        return replacedFormula.hashCode();
    }
}
