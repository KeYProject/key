// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
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

import de.uka.ilkd.key.proof.decproc.DecisionProcedureSmtAufliaOp;


/** Represents an uninterpreted function term as defined in the SMT-Lib specification,
 * and specialized in the (QF_)AUFLIA sublogic.
 * <p>
 * Each uninterpreted function is identified by its function name, which is an arbitrary legal
 * identifier <tt>String</tt>. An identifier is legal in (QF_)AUFLIA if it begins with a letter and
 * consists only of letters, digits and the characters '.' , '_' and ''' (single quotation mark).
 * <p>
 * UninterpretedFuncTerms are immutable; their attribute values cannot be changed after they
 * are created. 
 * 
 * @author akuwertz
 * @version 1.5,  12/04/2005  (Adjustments to changes in superclass; added further comments)
 */

public final class UninterpretedFuncTerm extends Term {

    /* Additional fields */
    
    /** The signature of this uninterpreted function */
    private final Signature signature;
    
    /** A int to cache the hash code for this <tt>UninterpretedFuncTerm</tt> */
    private int cachedHashCode;
    
    
    /* String constants for failures during Term creation */
    private static final String creationFailurefNameNull = "Function name is null!";
    private static final String 
        creationFailurefNameIllgSymb = "Function name is no legal identifier!";
    private static final String 
        creationFailurefArgsContNull = "Function argument array contains a null pointer at position !";
    private static final String creationFailureSigNull = "Signature is null!";
    private static final String creationFailureArity = "Argument count does not match signature!";
    private static final String creationFailureInterpreted = "Operator is interpreted!";
    
    
    
    /* Constructor */
    
    /** Creates a new <tt>UninterpretedFuncTerm</tt>, representing an uninterpreted function.
     * <p>
     * Every uninterpreted function is associated with a signature. It contains one more sort symbol
     * than the function contains arguments; the last sort symbol represents the return type of this
     * <tt>UninterpretedFuncTerm</tt>
     * <p>
     * To create an uninterpreted constant, <tt>fArgs</tt> can be either <tt>null</tt> or an empty
     * array; choosing <tt>null</tt> reduces the memory footprint through shared objects  
     * 
     * @param fName the name of the uninterpreted function
     * @param fArgs the array of function arguments 
     * @param sig the signature of this uninterpreted function
     * @throws NullPointerException if <tt>fName</tt> or <tt>sig</tt> is <tt>null</tt>
     *                              or if <tt>fArgs</tt> contains a null pointer
     * @throws IllegalArgumentException if <tt>fName</tt> is no legal identifier in (QF_)AUFLIA or
     *                                  if it equals an interpreted symbol or if the given signature
     *                                  does not match the function argument count 
     */
    public UninterpretedFuncTerm( String fName, Term[] fArgs, Signature sig ) {
        super( fName, fArgs, Term.marker , null );
        
        // Check if fName is syntactically correct and if arguments are not null
        if ( fName == null ) throw new NullPointerException( creationFailurefNameNull );
        if ( ! isLegalIdentifier( fName ) )
                throw new IllegalArgumentException( creationFailurefNameIllgSymb );
        if ( fArgs != null ) {
            for ( int i = 0; i < fArgs.length; i++ ) 
                if ( fArgs[i] == null ) 
                    throw new NullPointerException( creationFailurefArgsContNull + i );
        }
        if ( sig == null ) throw new NullPointerException( creationFailureSigNull );
        
        // Check that fName doesn't equal an interpreted symbol
        String[] interpretedOps = DecisionProcedureSmtAufliaOp.getAllSmtOperators();
        for( int i = 0; i < interpretedOps.length; i++ ) {
            if ( fName.equals( interpretedOps[i] ) )  
                throw new IllegalArgumentException( creationFailureInterpreted );           
        }
        
        // Check if signature and arguments match
        if ( fArgs == null ) {
            if ( sig.getLength() != 1 ) throw new IllegalArgumentException( creationFailureArity ); 
        } else if ( fArgs.length + 1 != sig.getLength() ) { 
            throw new IllegalArgumentException( creationFailureArity );
        }
        
        // Ok, set additional fields: signatures are immutable
        signature = sig;
    }
    
    
    
    // Public method implementation
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Term#equals(de.uka.ilkd.key.proof.decproc.smtlib.Term)
     */
    public boolean equals( Object o ) {
        if ( this == o ) return true;
        if ( super.equals( o ) ) {
            if ( o instanceof UninterpretedFuncTerm ) {
                UninterpretedFuncTerm t = ( UninterpretedFuncTerm ) o;
                return signature.equals( t.getSignature() );
            }
        }
        return false;
    }


    /** Returns an int value representing the hash code of this <tt>UninterpretedFuncTerm</tt>.
     * <p>
     * This hash code is calculated by combining the <tt>Term</tt> hash code of this
     * <tt>UninterpretedFuncTerm</tt> with the hash code of its <tt>Signature</tt>
     *  
     * @return the hash code of this <tt>UninterpretedFuncTerm</tt>
     */
    public int hashCode() {
        if ( cachedHashCode == 0 ) {
            cachedHashCode = 37*super.hashCode() + signature.hashCode();
        }
        return cachedHashCode;
    }

    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Term#toString()
     */
    public String toString() {
        Term[] thisFuncArgs = getFuncArgs();
        // An uninterpreted constant has got no brackets
        if ( thisFuncArgs.length == 0 ) return getFunction();
        String representation = "(" + getFunction();                    
        for ( int i = 0; i < thisFuncArgs.length; i++ ) {
            representation += " " + thisFuncArgs[i].toString();
        }        
        representation += ")";
        return representation;
    }
    
    
    /** Returns the signature of this <tt>UninterpretedFuncTerm</tt>
     * 
     * @return the signature of this <tt>UninterpretedFuncTerm</tt>
     */
    public Signature getSignature() {
        return signature;
    }


    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Term#replaceTermVar(de.uka.ilkd.key.proof.decproc.smtlib.TermVariable, de.uka.ilkd.key.proof.decproc.smtlib.Term)
     */
    public Term replaceTermVar( TermVariable termVar, Term replacement ) {
        if ( ! containsTerm( termVar ) ) return this;
        Term[] newSubterms = getFuncArgs();
        for ( int i = 0; i < newSubterms.length; i++ ) {            
            newSubterms[i] = newSubterms[i].replaceTermVar( termVar, replacement );            
        }
        return new UninterpretedFuncTerm( getFunction() , newSubterms, signature );
    }


    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Term#replaceFormVarIteTerm(de.uka.ilkd.key.proof.decproc.smtlib.FormulaVariable, de.uka.ilkd.key.proof.decproc.smtlib.Formula)
     */
    public Term replaceFormVarIteTerm( FormulaVariable formVar, Formula replacement ) {
        if ( ! containsFormulaIteTerm( formVar ) ) return this;
        Term[] newFuncArgs = getFuncArgs();
        for ( int i = 0; i < newFuncArgs.length; i++ ) {
            newFuncArgs[i] = newFuncArgs[i].replaceFormVarIteTerm( formVar , replacement );             
        }
        return new UninterpretedFuncTerm( getFunction(), newFuncArgs, signature );
    }
}
