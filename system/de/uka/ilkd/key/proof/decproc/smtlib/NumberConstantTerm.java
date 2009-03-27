// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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

import java.math.BigInteger;
import java.util.HashMap;


/** Represents a non negative integer number constant as defined in the SMT-Lib specification
 * and specialized in the (QF_)AUFLIA sublogic. Thereby number constants are terms.
 * <p>
 * NumberConstantTerms are immutable; their attribute values cannot be changed after they are
 * created. Due to this immutability, created instances of this class can be cached internally
 * 
 * @author akuwertz
 * @version 1.5,  01/31/2006  (Added support for BigIntegers)
 */

public final class NumberConstantTerm extends Term {

    /* Additional fields */
    private static final String creationFailure = "Number constant must be non negative!";
    
    /** A cache for created <tt>NumberConstantTerm</tt> objects, provided to reduce memory
     * footprint */
    private static final HashMap objectCache = new HashMap();
    
    
    
    /* Constructor */
    
    /** Creates a new <tt>NumberConstantTerm</tt>, representing an non negative integer constant
     * 
     * @param numberConstant the integer constant to be represented
     * @throws IllegalArgumentException if <tt>numberConstant</tt> is negative
     */
    public NumberConstantTerm( BigInteger numberConstant ) {
        super( numberConstant.toString() , null , null , null );
        if ( numberConstant.signum() == -1 ) throw new IllegalArgumentException( creationFailure );
    }
    
    
    
    /* Public methods implementation */

    /** A factory method that returns an instance of <tt>NumberConstantTerm</tt>, which represents
     * the specified non negative integer constant.
     * <p>
     * Calling this method has mostly the same effect as using the constructor of 
     * <tt>NumberConstantTerm</tt>, with the only difference that this method caches the created
     * objects. This means that every object returned by this method is cached internally; successive
     * calls of this method with same integer arguments result in same <tt>NumberConstantTerm</tt>
     * objects.
     * <p>
     * This cache is provided to reduce memory footprint. It can be cleared using the 
     * <tt>clearNumConstCache()</tt> method
     * 
     * @param numberConstant the <tt>BigInteger</tt> number constant to be represented
     * @return a <tt>NumberConstantTerm</tt> representing the specified number constant
     * @throws IllegalArgumentException if <tt>numberConstant</tt> is negative 
     * 
     * @see #clearNumConstCache()
     */
    public static NumberConstantTerm getInstance( BigInteger numberConstant ) {
        if ( numberConstant.signum() == -1 ) throw new IllegalArgumentException( creationFailure );
        if ( objectCache.containsKey( numberConstant ) ) {
            return ( NumberConstantTerm ) objectCache.get( numberConstant );
        }
        NumberConstantTerm newNumConstTerm = new NumberConstantTerm( numberConstant );
        objectCache.put( numberConstant , newNumConstTerm );
        return newNumConstTerm;
    }
    
    
    /** Clear the internal cache for <tt>NumberConstantTerm</tt> objects created with the
     * <tt>NumberConstantTermInstance</tt> method
     *
     *@see #getInstance( BigInteger )
     */ 
    public static void clearNumConstCache() {
        objectCache.clear();
    }
    
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Term#equals(de.uka.ilkd.key.proof.decproc.smtlib.Term)
     */
    public boolean equals( Object o ) {
        if ( o == this ) return true;
        if ( super.equals( o ) ) {
            return o instanceof NumberConstantTerm;
        }
        return false;
    }
    
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Term#hashCode()
     */
    public int hashCode() {
        return super.hashCode();
    }


    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Term#toString()
     */
    public String toString() {
        return getFunction();
    }
    
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Term#replaceTermVar(de.uka.ilkd.key.proof.decproc.smtlib.TermVariable, de.uka.ilkd.key.proof.decproc.smtlib.Term)
     */
    public Term replaceTermVar( TermVariable termVar, Term replacement ) {
        // A NumberConstant cannot contain any TermVariable
        return this;
    }


    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Term#replaceFormVarIteTerm(de.uka.ilkd.key.proof.decproc.smtlib.FormulaVariable, de.uka.ilkd.key.proof.decproc.smtlib.Formula)
     */
    public Term replaceFormVarIteTerm( FormulaVariable formVar, Formula replacement ) {
        return this;
    }
}
