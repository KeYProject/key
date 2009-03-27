// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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

import java.util.Vector;

import de.uka.ilkd.key.proof.decproc.DecisionProcedureSmtAufliaOp;

/** Represents an interpreted function as defined in the SMT-Lib specification, 
 * and specialized in the (QF_)AUFLIA sublogic. In (QF_)AUFLIA, only + , - , unary 
 * minus, * , 'select' (array) and 'store' (array) are interpreted functions.
 * <p>
 * InterpretedFuncTerms are immutable; their attribute values cannot be changed after they
 * are created.
 *  
 * @author akuwertz
 * @version 1.4,  12/04/2005  (Adjustments to changes in superclass; added further comments)                   
 */

public final class InterpretedFuncTerm extends Term {

    /* Additional fields */
    
    /** A int used to cache the hash code of this <tt>InterpretedFuncTerm</tt> if it represents a
     * commutative function */
    private int cachedCommHashCode;
    
    /* String constants for failures during Term creation */
    private static final String creationFailurefNameNull = "Function name is null!";
    private static final String creationFailurefArgsNull = "Function argument array is null!";
    private static final String 
        creationFailurefArgsContNull = "Function argument array contains a null pointer at position ";
    private static final String creationFailureArity = "Argument count does not match function arity!";
    private static final String creationFailureArgType = "Argument types don't match function signature!";
    private static final String creationFailureUninterpreted = "Operator is not an interpreted one!";
    private static final String creationFailureArray = "First function argument must be of type 'array'!";
    private static final String 
        creationFailureInt = "Second and third function arguments must be of type 'int'!";
    private static final String creationFailureIntArb = "Function arguments must be of type 'int'!";
        
    
    
    /* Constructor */
    
    /** Creates a new <tt>InterpretedFuncTerm</tt>, representing an interpreted function as 
     * defined in (QF_)AUFLIA.
     * <p>
     * Which interpreted function is to be represented, is specified solely by the function name.
     * Therefore, only certain <tt>String</tt> values are accepted as interpreted functions in
     * (QF_)AUFLIA; they are defined as static fields in <tt>DecisionProcedureSmtAufliaOp</tt>. 
     * Namely, this are PLUS, MINUS, UMINUS, MULT, SELECT and STORE.
     * <p>
     * In (QF_)AUFLIA, there are two interpreted sorts, INT and ARRAY. For the mentioned interpreted
     * functions the following signatures hold:<br>
     *  UMINUS: INT->INT<br>
     *  MINUS: INT->INT->INT<br>
     *  PLUS: INT->INT->INT<br> 
     *  MULT: INT->INT->INT<br>
     *  SELECT: ARRAY->INT->INT<br>
     *  STORE: ARRAY->INT->INT->ARRAY<br>
     *  For convenience, the PLUS function allows also more than two arguments. The MULT function
     *  requests of one its arguments to be a natural number constant.<br>
     *  The sort of a <tt>Term</tt> depends on its class:
     *  A <tt>NumberConstantTerm</tt>is of sort Int, a <tt>Termvariable</tt>s of arbitrary sort.
     *  For an <tt>InterpretedFuncTerm</tt> or an <tt>UninterpretedFuncTerm</tt> the sort is
     *  determined by their signature. An <tt>IteTerm</tt> is of same sort as its argument 
     *  <tt>Term</tt>s.
     *  <p>
     *  If any of these conditions does not hold for the <tt>InterpretedFuncTerm</tt> to created,
     *  an <tt>IllegalArgumentException</tt> is thrown.
     *  
     * @param fName the name of the interpreted function to be represented
     * @param fArgs the array of function arguments; 
     * @throws NullPointerException if <tt>fName</tt> or <tt>fArgs </tt>is <tt>null</tt> or if
     *                              <tt>fArgs</tt> contains a null pointer
     * @throws IllegalArgumentException if <tt>fName</tt> is no interpreted function symbol in
     *                                  QF_AULIA or if the number of function arguments doesn't
     *                                  match the function arity or if the sort of a function 
     *                                  argument doesn't match the expected sort
     * @see de.uka.ilkd.key.proof.decproc.DecisionProcedureSmtAufliaOp                                   
     */ 
    public InterpretedFuncTerm( String fName, Term[] fArgs ) {        
        super( fName , fArgs, null , null );
        
        if ( fName == null ) throw new NullPointerException( creationFailurefNameNull );
        if ( fArgs == null ) throw new NullPointerException( creationFailurefArgsNull );
        for ( int i = 0; i < fArgs.length; i++ ) {
            if ( fArgs[i] == null ) 
                throw new NullPointerException( creationFailurefArgsContNull + i );
        }
        // Find out if the function fName is interpreted, and if so, check the arguments
        if ( fName == DecisionProcedureSmtAufliaOp.PLUS ) {
            if ( fArgs.length < 2 ) 
                throw new IllegalArgumentException( creationFailureArity );
            for ( int i = 0; i < fArgs.length; i++ ) {
                if ( ! isIntSort( fArgs[i] ) ) {
                    throw new IllegalArgumentException( creationFailureIntArb );
                }    
            }
            
        } else if ( fName == DecisionProcedureSmtAufliaOp.MINUS ) {
            if ( fArgs.length != 2 ) 
                throw new IllegalArgumentException( creationFailureArity );
            if ( ! isIntSort( fArgs[0] ) ) throw new IllegalArgumentException( creationFailureIntArb );
            if ( ! isIntSort( fArgs[1] ) ) throw new IllegalArgumentException( creationFailureIntArb );
            
        } else if ( fName == DecisionProcedureSmtAufliaOp.UMINUS ) {
            if ( fArgs.length != 1)
                throw new IllegalArgumentException( creationFailureArity );
            if ( ! isIntSort( fArgs[0] ) ) throw new IllegalArgumentException( creationFailureIntArb );
            
        } else if ( fName == DecisionProcedureSmtAufliaOp.MULT ) {
            if ( fArgs.length != 2 ) 
                throw new IllegalArgumentException( creationFailureArity );            
            if  ( !( fArgs[0] instanceof NumberConstantTerm | fArgs[1] instanceof NumberConstantTerm ) )
                throw new IllegalArgumentException( creationFailureArgType );
            if ( ! isIntSort( fArgs[0] ) ) throw new IllegalArgumentException( creationFailureIntArb );
            if ( ! isIntSort( fArgs[1] ) ) throw new IllegalArgumentException( creationFailureIntArb );
          
        } else if ( fName == DecisionProcedureSmtAufliaOp.SELECT ) {
            if ( fArgs.length != 2)
                throw new IllegalArgumentException( creationFailureArity );
            if ( ! isArraySort( fArgs[0] ) ) throw new IllegalArgumentException( creationFailureArray );
            if ( ! isIntSort( fArgs[1] ) ) throw new IllegalArgumentException( creationFailureInt );
            
        } else if ( fName == DecisionProcedureSmtAufliaOp.STORE ) {
            if ( fArgs.length != 3)
                throw new IllegalArgumentException( creationFailureArity );
            if ( ! isArraySort( fArgs[0] ) ) throw new IllegalArgumentException( creationFailureArray );
            if ( ! isIntSort( fArgs[1] ) ) throw new IllegalArgumentException( creationFailureInt );
            if ( ! isIntSort( fArgs[2] ) ) throw new IllegalArgumentException( creationFailureInt );            

            
        // No interpreted function    
        } else throw new IllegalArgumentException( creationFailureUninterpreted  );
    }
    
    
    
    // Public method implementation
    
    /** Compares this <tt>InterpretedFuncTerm</tt> to the specified <tt>Object</tt>.
     * <p>
     * This <tt>InterpretedFuncTerm</tt> is considered equal to <tt>o</tt> if <tt>o</tt> is an
     * instance of <tt>InterpretedFuncTerm</tt> and has the same function arguments as this
     * <tt>InterpretedFuncTerm</tt>. <br>
     * If the represented function is commutative, i.e. if this <tt>InterpretedFuncTerm</tt>
     * represents one of the functions 'PLUS' or 'MULT', the order of function arguments does
     * not matter for equality. For all other interpreted functions in (QF_)AUFLIA, the order of
     * arguments matters for equality.
     * 
     * @param o the <tt>Object</tt> to compare with
     * @return true if this <tt>InterpretedFuncTerm</tt> is the same as the <tt>Object</tt> o;
     *         otherwise false.
     */ 
    public boolean equals( Object o ) {
        if ( o == this ) return true;
        if ( o instanceof InterpretedFuncTerm ) {
            if ( super.equals( o ) ) return true;
            InterpretedFuncTerm t = ( InterpretedFuncTerm ) o;
            String thisFunction = super.getFunction(); 
            if ( thisFunction.equals( t.getFunction() ) ) {
                if (  thisFunction.equals( DecisionProcedureSmtAufliaOp.PLUS )
                    | thisFunction.equals( DecisionProcedureSmtAufliaOp.MULT ) ) {
                    // Two commutative functions are equal, if their set of arguments is the same                        
                    Vector thisArgs = toVector( super.getFuncArgs() );
                    Vector tArgs = toVector( t.getFuncArgs() );
                    if ( thisArgs.containsAll( tArgs ) && tArgs.containsAll( thisArgs ) ) {
                        return true;
                    }                                                            
                }
            }    
        } 
        return false;                                
    }


    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Term#hashCode()
     */
    public int hashCode() {
        String thisFunction = getFunction();
        // Non commutative functions
        if (  thisFunction.equals( DecisionProcedureSmtAufliaOp.MINUS )
            | thisFunction.equals( DecisionProcedureSmtAufliaOp.UMINUS )
            | thisFunction.equals( DecisionProcedureSmtAufliaOp.SELECT )
            | thisFunction.equals( DecisionProcedureSmtAufliaOp.STORE ) ) {
            return super.hashCode();
        }    
        // Commutative functions
        if ( cachedCommHashCode == 0 ) { 
            Term[] thisFuncArgs = getFuncArgs();
            int result = 17;
            result = 37*result + thisFunction.hashCode();
            int[] hashCodes = new int[ thisFuncArgs.length ];
            for ( int i = 0; i < thisFuncArgs.length; i++ ) {
                hashCodes[i] = thisFuncArgs[i].hashCode();                
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
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Term#toString()
     */
    public String toString() {
        String representation = "(" + getFunction();                
        Term[] thisFuncArgs = getFuncArgs();
        for ( int i = 0; i < thisFuncArgs.length; i++ ) {
            representation += " " + thisFuncArgs[i].toString();
        }    
        representation += ")";
        return representation;
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
        return new InterpretedFuncTerm( getFunction() , newSubterms );        
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
        return new InterpretedFuncTerm( getFunction(), newFuncArgs );
    }
    
    
    
    // Internal methods */
    
    /** Converts an array of <tt>Term</tt>s into a <tt>Vector</tt>, preserving element order
     *  
     * @param terms The array which should be converted into a <tt>Vector</tt> 
     * @return a <tt>Vector</tt> containing all the <tt>Term</tt>s in the specified array,
     *         in the same order
     */
    private Vector toVector( Term[] terms ) {
        Vector termVector = new Vector( terms.length );
        for ( int i = 0; i < terms.length; i++ ) {
            termVector.add( i, terms[i] );
        }
        return termVector;
    }
    
    
    /** Checks if the specified <tt>Term</tt> is of sort 'array', which is interpreted in (QF_)AUFLIA
     * 
     * @param t the <tt>Term</tt> to be checked for being of sort 'array' 
     * @return true iff the result of the function represented by this <tt>Term</tt> is of sort 'array'
     */    
    private boolean isArraySort( Term t ) {
        // Uninterpreted functions can have the return type 'array'
        if ( t instanceof UninterpretedFuncTerm ) {
            UninterpretedFuncTerm uiTerm = ( UninterpretedFuncTerm ) t;
            Signature uiSig = uiTerm.getSignature();
            if ( uiSig.getSymbols()[ uiSig.getLength()-1 ] == DecisionProcedureSmtAufliaOp.ARRAY ) {
                return true;
            }                 
        // As interpreted function only STORE returns an 'array'                  
        } else if ( t instanceof InterpretedFuncTerm ) {
            if ( t.getFunction() == DecisionProcedureSmtAufliaOp.STORE ) return true;
        // Both alternatives must be of type 'array'
        } else if ( t instanceof IteTerm ) {
            IteTerm ite = ( IteTerm )  t;
            return ( isArraySort( ite.getTermT1() )  &  isArraySort( ite.getTermT2() ) );
        // For a term variable, an arbitrary term could be set
        } else if ( t instanceof TermVariable ) return true;
        return false;        
    }
    
    
    /** Checks if the specified <tt>Term</tt> is of sort 'int', which is interpreted in (QF_)AUFLIA
     * 
     * @param t the <tt>Term</tt> to be checked for being of sort 'int' 
     * @return true iff the result of the function represented by this <tt>Term</tt> is of sort 'int'
     */
    private boolean isIntSort( Term t ) {
        // Uninterpreted functions can have the return type 'int'
        if ( t instanceof UninterpretedFuncTerm ) {
            UninterpretedFuncTerm uiTerm = ( UninterpretedFuncTerm ) t;
            Signature uiSig = uiTerm.getSignature();
            if ( uiSig.getSymbols()[ uiSig.getLength()-1 ] == DecisionProcedureSmtAufliaOp.INT ) {
                return true;
            } 
            return false;     
        // As interpreted function only STORE returns an 'array'                  
        } else if ( t instanceof InterpretedFuncTerm ) {
            if ( t.getFunction() == DecisionProcedureSmtAufliaOp.STORE ) return false;    
        // Both alternatives must be of type 'int'
        } else if ( t instanceof IteTerm ) {
            IteTerm ite = ( IteTerm )  t;
            return ( isIntSort( ite.getTermT1() )  &  isIntSort( ite.getTermT2() ) );
        } 
        // Number constants are of type 'int', term variables can be
        return true;           
    }
}
