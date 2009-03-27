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

/** Represents a truth value as defined in the SMT-Lib specification, and specialized in the
 * (QF_)AUFLIA sublogic.
 * <p>
 * Thereby 'true' and 'false' are the only truth value constants allowed in (QF_)AUFLIA.
 * <p>
 * TruthValueFormula are immutable; their attribute values cannot be changed after they are
 * created. Due to their immutability, <tt>TruthValueFormula</tt> instances can be cached
 *  
 * @author akuwertz
 * @version 1.3,  12/09/2005  (Adjustments to superclass V1.5)
 */

public final class TruthValueFormula extends Formula {

    /* Additional fields */
    
    /** A cache for the two unequal <tt>TruthValueFormula</tt> instances */ 
    private static final TruthValueFormula[] instanceCache = new TruthValueFormula[2];
    
    
    
    /* Constructor */
    
    /** Creates a <tt>TruthValueFormula</tt>, representing the given truth value
     *  
     * @param value the truth value to be represented
     */
    public TruthValueFormula( boolean value ) {
        super( value ?  DecisionProcedureSmtAufliaOp.TRUE : DecisionProcedureSmtAufliaOp.FALSE ,
               null, null );
    }
    
    
    
    /* Public method implementation */
    
    /** A factory method returning for instances of <tt>TruthValueFormula</tt>.
     * <p>
     * The instances returned by this method are cached to reduce memory footprint. Therefore
     * successive calls with the same truth value result in the same object being returned.
     * 
     * @param value the truth value to be represented
     * @return a <tt>TruthValueFormula</tt> instance representing <tt>value</tt>
     */ 
    public static TruthValueFormula getInstance( boolean value ) {
        int index = value ? 1 : 0;
        if ( instanceCache[ index ] == null ) 
            instanceCache[ index ] = new TruthValueFormula( value );
        return instanceCache[ index ];
    }
      
    
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
        return getOp();
    }


    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Formula#replaceFormVar(de.uka.ilkd.key.proof.decproc.smtlib.FormulaVariable, de.uka.ilkd.key.proof.decproc.smtlib.Formula)
     */
    public Formula replaceFormVar( FormulaVariable formVar, Formula replacement ) {
        // A TruthValue cannot contain any FormulaVariable
        return this;
    }


    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Formula#replaceTermVar(de.uka.ilkd.key.proof.decproc.smtlib.TermVariable, de.uka.ilkd.key.proof.decproc.smtlib.Term)
     */
    public Formula replaceTermVar( TermVariable termVar, Term replacement ) {
        // A TruthValue cannot contain any TermVariable
        return this;
    }
}
