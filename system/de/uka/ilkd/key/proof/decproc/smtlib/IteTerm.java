// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//              Universitaet Koblenz-Landau, Germany
//              Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.decproc.smtlib;

import de.uka.ilkd.key.proof.decproc.DecisionProcedureSmtAufliaOp;


/** Represents an if-then-else (ite) construct for terms as defined in the SMT-Lib 
 * specification, and specialized in the (QF_)AUFLIA sublogic. Thereby an ite-construct 
 * consists of a formula 'iteFormula' and two terms t1 and t2, and evaluates to one of
 * this terms in dependence of the truth value of the formula.
 * <p>
 * IteTerms are immutable; their attribute values cannot be changed after they are created.
 *  
 * @author akuwertz
 * @version 1.4,  12/05/2005  (Adjustments to changes in superclass; further comments)
 */

public final class IteTerm extends Term {

    /* Additional fields */
    
    /** The <tt>Formula</tt> of this Term */
    private final Formula iteFormula;
    
    /** A int to cache the hash code for this <tt>IteTerm</tt> */
    private int cachedHashCode;
    
    // String constants for failures during Term creation
    private static final String creationFailureT1Null = "Term t1 is null!";
    private static final String creationFailureT2Null = "Term t2 is null!";
    private static final String creationFailureFormula1Null = "Formula is null!";
    
    
    
    /* Constructor */
    
    /** Creates an new <tt>IteTerm</tt>.
     * <p>
     * An <tt>IteTerm</tt> consists of one <tt>Formula</tt> and two <tt>Term</tt>s. It is 
     * semantically equivalent to its first or second <tt>Term</tt> argument in dependence of
     * the truth value of its <tt>Formula</tt>. 
     * 
     * @param t1 the <tt>Term</tt> into which this <tt>IteTerm</tt> results if its <tt>Formula</tt>
     *           is evaluated to true 
     * @param t2 the <tt>Term</tt> into which this <tt>IteTerm</tt> results if its <tt>Formula</tt>
     *           is evaluated to false
     * @param iteForm the <tt>Formula</tt> to be evaluated 
     * @throws NullPointerException if one of the specified arguments is <tt>null</tt> 
     */
    public IteTerm( Term t1, Term t2, Formula iteForm ) {
        super( DecisionProcedureSmtAufliaOp.ITE , 
               new Term[]{ t1, t2 } , iteForm != null ? iteForm.getUIF() : null ,
                                      iteForm != null ? iteForm.getUIPredicates() : null );    
        if ( t1 == null ) throw new NullPointerException( creationFailureT1Null);
        if ( t2 == null ) throw new NullPointerException( creationFailureT2Null);
        if ( iteForm == null ) throw new NullPointerException( creationFailureFormula1Null );        
        iteFormula = iteForm;
    }
    
    
    
    // Public method implementations
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Term#containsTerm(de.uka.ilkd.key.proof.decproc.smtlib.Term)
     */
    public boolean containsTerm( Term t ) {
        if ( super.containsTerm( t ) ) return true;
        return iteFormula.containsTerm( t );
    }
    
    
    /** Returns true if this <tt>IteTerm</tt> contains the specified <tt>Term</tt> t as a subterm
     * of one of its <tt>Term</tt> arguments, i.e. if t is contained in t1 or t2. In contrast to 
     * <tt>containsTerm</tt>, the iteFormula is not checked for containment of t.
     * 
     * @param t the <tt>Term</tt> to be checked for containment in this <tt>IteTerm</tt>
     * @return true if t is contained in of one the subterms of this <tt>IteTernm</tt>
     */
    public boolean containsTermAsSubterm( Term t ) {               
        Term[] thisFuncArgs = getFuncArgs();
        for ( int i = 0; i < thisFuncArgs.length; i++ ) {
            if ( thisFuncArgs[i].containsTerm( t ) ) return true;
        }
        return false;
    }

    
    /** Returns true if this <tt>IteTerm</tt> contains the specified <tt>Formula</tt> f
     * in its ite-formula
     *  
     * @param f the <tt>Formula</tt> to be checked for containment in this <tt>IteTerm</tt>
     * @return true if this <tt>IteTerm</tt> contains the <tt>Formula</tt> f. 
     */
    public boolean containsFormulaIteTerm( Formula f ) {
        if ( super.containsFormulaIteTerm( f ) ) return true;        
        return iteFormula.containsFormula( f );
    }
    
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Term#equals(de.uka.ilkd.key.proof.decproc.smtlib.Term)
     */
    public boolean equals( Object o ) {
        if ( this == o ) return true;
        if ( super.equals( o ) ) {
            if ( o instanceof IteTerm ) {
                IteTerm t = ( IteTerm ) o;
                return iteFormula.equals( t.getIteFormula() );
            }    
        }    
        return false;
    }


    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Term#hashCode()
     */
    public int hashCode() {
        if ( cachedHashCode == 0 ) {
           cachedHashCode = 37*super.hashCode() + iteFormula.hashCode();     
        }
        return cachedHashCode;
    }

    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Term#toString()
     */
    public String toString() {
        String representation = "(" + getFunction();        
        representation += " " + iteFormula.toString() + " ";
        representation += getFuncArgs()[0].toString() + " " + getFuncArgs()[1].toString();        
        representation += ")";
        return representation;
    }
    
    
    /** Returns the Formula of this <tt>IteTerm</tt>.
     * 
     * @return the Formula of this <tt>IteTerm</tt>
     */
    public Formula getIteFormula() {
        return iteFormula;        
    }
    
    
    /** Returns the <tt>Term</tt> t1 of this <tt>IteTerm</tt>
     *  
     * @return the <tt>Term</tt> t1 of this <tt>IteTerm</tt>
     */
    public Term getTermT1() {
        return getFuncArgs()[0]; 
    }
    
    
    /** Returns the <tt>Term</tt> t2 of this <tt>IteTerm</tt>
     *  
     * @return the <tt>Term</tt> t2 of this <tt>IteTerm</tt>
     */
    public Term getTermT2() {
        return getFuncArgs()[1]; 
    }

    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Term#replaceTermVar(de.uka.ilkd.key.proof.decproc.smtlib.TermVariable, de.uka.ilkd.key.proof.decproc.smtlib.Term)
     */
    public Term replaceTermVar( TermVariable termVar, Term replacement ) {
        if ( ! containsTerm( termVar ) ) return this;
        Term[] thisFuncArgs = getFuncArgs();
        return new IteTerm( thisFuncArgs[0].replaceTermVar( termVar, replacement ) ,
                            thisFuncArgs[1].replaceTermVar( termVar, replacement ) ,
                            iteFormula.replaceTermVar( termVar, replacement ) );
    }
    
    
    /** Replaces all occurrences of a specified <tt>FormulaVariable</tt> by a specified
     * <tt>Formula</tt> in the iteFormula of this <tt>IteTerm</tt>.
     * Thereby this <tt>IteTerm</tt> and the returned replaced <tt>Term</tt> share the
     * same objects in their fields, except for those objects which contained the
     * specified <tt>FormulaVariable</tt>
     *   
     * @param formVar the <tt>FormulaVariable</tt> to be replaced
     * @param replacement the <tt>Formula</tt> used to replace <tt>formVar</tt>
     * @return the <tt>Formula</tt> obtained by replacing every (free) occurence of <tt>formVar</tt>
     *         by <tt>replacement</tt> in the iteFormula of this <tt>IteTerm</tt>     
     */
    public Term replaceFormVarIteTerm( FormulaVariable formVar, Formula replacement ) {
        if ( ! containsFormulaIteTerm( formVar ) ) return this;
        Term[] thisFuncArgs = getFuncArgs();
        return new IteTerm( thisFuncArgs[0].replaceFormVarIteTerm( formVar, replacement ) ,
                            thisFuncArgs[1].replaceFormVarIteTerm( formVar, replacement )  , 
                            iteFormula.replaceFormVar( formVar, replacement) );
    }
}
