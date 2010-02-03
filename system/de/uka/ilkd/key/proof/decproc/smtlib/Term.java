// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                  Universitaet Koblenz-Landau, Germany
//                  Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.decproc.smtlib;

import java.util.HashSet;
import java.util.Vector;

/**
 * Represents a term as defined in the SMT-Lib specification, and specialized in the
 * QF_AUFLIA sublogic. Thereby, a term represents a function in most cases. It is constructed
 * recursively out of other terms, which are known as its the function arguments, and a String
 * representing the function name.  
 * <p>
 * This class is abstract because it is intended as a frame for realizing subclasses which 
 * specialize in representing one class of functions in QF_AUFLIA (e.g. uninterpreted functions).
 * <p> 
 * Term objects are intentionally immutable; their attribute values cannot be changed once they are
 * created. 
 * <p>
 * This class also contains methods with protected access intended to be used by realizing
 * subclasses for convenience, as well as methods to access a list of all uninterpreted functions
 * and predicates contained in this term, which are provided for the simple integration of terms
 * into a formulae and benchmarks.
 * 
 * @author akuwertz
 * 
 * @version 1.5,  12/04/2005  (Added further API comments)
 * 
 * @see <a href="http://goedel.cs.uiowa.edu/smtlib/logics/QF_AUFLIA.smt">QF_AUFLIA</a>
 * @see <a href="http://goedel.cs.uiowa.edu/smtlib">SMT-LIB</a>
 */

public abstract class Term {
    
    /** The function name of this <tt>Term</tt> */ 
    private final String function;
    
    /** The array of function arguments of this <tt>Term</tt> */
    private final Term[] funcArgs;
    
    /** A template <tt>Term</tt> array assigned to <tt>funcArgs</tt> if this <tt>Term</tt> has no 
     * function arguments. This shared object is intended to lower memory footprint */       
    private static final Term[] emptyTermArray = new Term[0];
    
    /** The <tt>Vector</tt> of all uninterpreted functions contained in this <tt>Term</tt> */
    private final Vector uninterFuncs;
    
    /** The <tt>Vector</tt> of all uninterpreted predicates contained in this <tt>Term</tt>.
     * This fields was included to support ite-constructs */ 
    private final Vector uninterPredsIteTerm;
    
    /** A template <tt>Vector</tt> assigned to the <tt>Term</tt> attributes which store the
     * uninterpreted functions and predicates of this <tt>Term</tt>, if these fields are empty.
     * This shared object is intended to lower memory footprint */      
    private static final Vector emptyVector = new Vector();
    
    /** The cached hash code for this <tt>Term</tt> */     
    private final int hashCode;
        
    /** A <tt>Vector</tt> serving as an unique marker object. It is used by subclasses as an
     * argument of the <tt>Term</tt> constructor to indicate to the constructor that a reference to
     * the calling subclass instance must be contained in the uninterpreted functions field of the
     * <tt>Term</tt> to be created 
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Term#Term(String, de.uka.ilkd.key.proof.decproc.smtlib.Term[], java.util.Vector, java.util.Vector) 
     */
    protected static final Vector marker = new Vector();
    
    
    
    /* Constructor */
    
    /** Sole constructor. For invocation by constructors of realizing subclasses.
     * <p>
     * This explicit constructor sets the internal fields to the specified values or rather to 
     * values computed out of the given ones. Thereby the function name and the function arguments
     * are set directly, whereby the <tt>Vector</tt> of uninterpreted functions and predicates
     * resprectively are computed out of the specified <tt>Vector</tt>s and the uninterpreted functions contained in
     * the function arguments (respectively predicates).<br> 
     * Therefor all function argument <tt>Term</tt>s are searched for uninterpreted functions 
     * (respectively predicates) and the results are merged into a <tt>Vector</tt>, eleminating
     * duplicate entries.<br> 
     * To enable realizing subclasses to specify further uninterpreted functions or predicates
     * contained in this <tt>Term</tt> (which can not be computed from its function arguments), the
     * argument <tt>Vector</tt>s <tt>addUifs</tt> and <tt>addUips</tt> are provided. Their elements
     * are merged into the result <tt>Vector</tt>s as their first elements, preserving their given
     * order.<br> 
     * Therefore, they must not contain duplicate elements. If set to <tt>null</tt> they indicate
     * that there are no additional uninterpreted functions and predicates respectively.
     * <p>
     * The argument <tt>Vector</tt> <tt>addUifs</tt> inheres a additional function. It can serve as
     * an indicator to the constructor that the calling subclass instance wishes to be added to the
     * <tt>Vector</tt> of uninterpreted functions. If the specified <tt>Vector</tt> instance is the
     * <tt>Vector</tt> contained in the static field <tt>marker</tt>, the calling instance will be 
     * added to the <tt>Vector</tt> of uninterpreted functions as its first element.
     * <p> 
     * This implementation checks for null pointers in the specified arguments. As mentioned above,
     * null pointers are explicitly allowed in <tt>addUifs</tt> and <tt>addUips</tt> for
     * convenience.<br>
     * No null pointers are allowed in the function name argument <tt>fName</tt>. If a null pointer
     * is found, all fields will be set to <tt>null</tt> without throwing any exceptions. This
     * is done to enable realizing subclasses to throw specific exceptions on their part. It 
     * implicates that every subclass realizing this class must check <tt>fName</tt> for being a
     * null pointer, and, if so, throw an exception. Otherwise <tt>Term</tt> methods called on the
     * created subclass instance could fail with a <tt>NullPointerException</tt>.<br>
     * The same holds for the <tt>Term</tt>s contained in the array of function arguments 
     * <tt>fArgs</tt>. If the specified array contains any null pointers, the <tt>Term</tt> fields
     * will be set to <tt>null</tt> without throwing an exception. Realizing subclasses therefore
     * have to check or ensure that <tt>fArgs</tt> contains no null pointers; otherwise the 
     * <tt>Term</tt> methods could fail with a <tt>NullPointerException</tt>.<br>
     * In contrary to this, a null pointer is allowed for the array object itself. This is done for
     * convenience and has to same effects as an empty array would have.
     *  
     * @param fName the function name of this <tt>Term</tt> 
     * @param fArgs the array of function arguments for this <tt>Term</tt>
     * @param addUifs the Vector containing these <tt>Term</tt>s that should be merged into the
     *                <tt>Vector</tt> of uninterpreted functions additionally. It may be null and
     *                must not contain any duplicates.
     * @param addUips the Vector containing these <tt>Formula</tt>e that should be merged into the
     *                <tt>Vector</tt> of uninterpreted predicates additionally. It may be null and
     *                must not contain any duplicates. 
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Term#marker
     */
    protected Term( String fName, Term[] fArgs, Vector addUifs, Vector addUips ) {
        
        if ( fName == null ) {
            function = null;
            funcArgs = null;
            uninterFuncs = uninterPredsIteTerm = null;
            hashCode = 0;
            // Handling of this null pointer situation has to be done by subclass
            return;
        }
        function = fName;
        
        // Null pointer for fArgs is allowed for convenience
        // Given array is cloned for immutability (exclusiveness)
        if ( fArgs == null  ||  fArgs.length == 0 ) funcArgs = emptyTermArray;  
        else funcArgs = ( Term [] ) fArgs.clone();
                        
        // Estimate capacity of new uif and uip Vectors to reduce reallocation effects to one
        int estSizeUif = 0, estSizeUip = 0;
        Vector[] uifHelper = new Vector[ funcArgs.length ];
        Vector[] uipHelper = new Vector[ funcArgs.length ];

        try {
            for ( int i = 0; i < funcArgs.length; i++ ) {
                uifHelper[i] = funcArgs[i].getUIF();
                uipHelper[i] = funcArgs[i].getUIPredicatesIteTerm();                
                estSizeUif += uifHelper[i].size();
                estSizeUip += uipHelper[i].size();
            }
        } catch (NullPointerException e ) {
            uninterFuncs = uninterPredsIteTerm = null;
            hashCode = 0;
            // Handling of this null pointer situation has to be done by subclass
            return;
        }
        
        // Compute Vector of uninterpreted functions contained in this Term
        if ( ( addUifs == null  ||  ( addUifs.size() == 0  &&  addUifs != marker ) )
            &&  estSizeUif == 0 ) { 
            // If no uninterpreted functions contained, use empty template Vector
            uninterFuncs = emptyVector;
        } else {
            // Compute Vector lengths and Vector elements, i.e. uninterpreted functions
            HashSet contFuncNames = new HashSet( estSizeUif + 1 );
            // Create new Vector of estimated capacity
            if ( addUifs == null ) addUifs = new Vector( estSizeUif );
            /*  If the specified Vector is the marker Vector, make sure uninterFuncs contains a
             * refenrence to itself */
            else if ( addUifs == marker ) {
                addUifs = new Vector( estSizeUif + 1);
                addUifs.add( this );
                contFuncNames.add( function );
            } else {
                if ( addUifs.size() != 0 ) {
                    if ( addUifs.size() < estSizeUif ) {            
                        Vector temp = addUifs;
                        addUifs = new Vector ( estSizeUif + temp.size() );
                        addUifs.addAll( temp );
                    } else {
                        addUifs.ensureCapacity( estSizeUif + addUifs.size() );
                    }
                    for ( int i = 0; i < addUifs.size(); i++ ) {
                        contFuncNames.add( ( ( Term ) addUifs.get(i) ).getFunction() );
                    }
                }
                addUifs.ensureCapacity( estSizeUif ) ;
            }
            Vector uifVector;
            for ( int i = 0; i < uifHelper.length; i++ ) {
              uifVector = uifHelper[i];
                for( int j = 0; j < uifVector.size(); j++ ) {
                    if ( contFuncNames.add( ( ( Term ) uifVector.get(j) ).getFunction() ) ) {
                        addUifs.add( uifVector.get(j) );
                    }
                }
            }
            addUifs.trimToSize();
            uninterFuncs = addUifs;
        }
        
        // Compute Vector of uninterpreted predicates contained in this Term
        if ( ( addUips == null  ||  addUips.size() == 0 )  &&  estSizeUip == 0 ) { 
            // If no uninterpreted predicates contained, use empty template Vector
            uninterPredsIteTerm = emptyVector;
        } else {
            // Compute Vector lengths and create Vector of appropriate size and
            // prepare the HashSet with the given ui predicate names
            HashSet contPredNames = new HashSet( estSizeUip );
            if ( addUips == null ) addUips = new Vector( estSizeUip );
            else if ( addUips.size() != 0 ) {
                if ( addUips.size() < estSizeUip ) {            
                    Vector temp = addUips;
                    addUips = new Vector ( estSizeUip + temp.size() );
                    addUips.addAll( temp );
                } else {
                    addUips.ensureCapacity( estSizeUip + addUips.size() );
                }
                for ( int i = 0; i < addUips.size(); i++ ) {
                    contPredNames.add( ( ( Formula ) addUips.get(i) ).getOp() );
                }
            }
            addUips.ensureCapacity( estSizeUip ) ;
            // Compute contained ui predicates
            Vector uipVector;
            for ( int i = 0; i < uipHelper.length; i++ ) {
              uipVector = uipHelper[i];
                for( int j = 0; j < uipVector.size(); j++ ) {
                    if ( contPredNames.add( ( ( Formula ) uipVector.get(j) ).getOp() ) ) {
                        addUips.add( uipVector.get(j) );
                    }
                }
            }
            addUips.trimToSize();
            uninterPredsIteTerm = addUips;            
        }
        
        // Calculate hash code for a Term
        int result = 17;
        result = 37*result + function.hashCode();
        for ( int i = 0; i < funcArgs.length; i++ ) {
            result = 37*result + funcArgs[i].hashCode();
        }        
        hashCode = result;
    }
    
    
    
    /* Now the public methods */       

    /** Returns the function name of this <tt>Term</tt> 
     *
     * @return the function name of this <tt>Term</tt>
     */
    public final String getFunction() {
        return function;         
    }  


    /** Returns a shallow copy of the function argument array of this <tt>Term</tt>
     * 
     * @return the array of function arguments of this <tt>Term</tt>
     */
    public final Term[] getFuncArgs() {        
        return ( Term[] ) funcArgs.clone();        
    }
    

    /** Returns a <tt>Vector</tt> of all uninterpreted functions contained in this <tt>Term</tt>,
     * as a shallow copy
     * 
     * @return a <tt>Vector</tt> of all uninterpreted functions contained in this <tt>Term</tt>
     */ 
    public final Vector getUIF() {
        return ( Vector )uninterFuncs.clone();
    }

    
    /** Returns a <tt>Vector</tt> of all uninterpreted predicates contained in this <tt>Term</tt>,
     * as a shallow copy
     * 
     * @return an <TT>Vector</tt> of all uninterpreted predicates contained in this <tt>Term</tt>
     */ 
    public final Vector getUIPredicatesIteTerm() {       
        return ( Vector ) uninterPredsIteTerm.clone();
    }
 
    
    /** Returns true if this <tt>Term</tt> contains the <tt>Term</tt> <tt>t</tt>.
     * <p>
     * This implementation tries to determine containment by first checking if t <tt>equals</tt>
     * this <tt>Term</tt>. If not, it calls <tt>containsTerm</tt> recursively on the function
     * argument <tt>Term</tt>s of this <tt>Term</tt> and returns true, if one of the function 
     * arguments contains <tt>t</tt>
     *  
     * @param t the <tt>Term</tt> to be checked for containment in this <tt>Term</tt>
     * @return true if this <tt>Term</tt> contains t; otherwise false
     */
    public boolean containsTerm( Term t ) {
        // t is contained if it is equal
        if ( equals( t ) ) return true;
        // t could also be contained in function argument        
        for ( int i = 0; i < funcArgs.length; i++ ) {
            if ( funcArgs[i].containsTerm( t ) ) return true;
        }
        return false;
    }
    
    
    /** Returns true if this <tt>Term</tt> contains the <tt>Formula</tt> f.
     * <p>
     * This implementation tries to determine containment by calling <tt>containsFormulaIteTerm</tt>
     * recursively on the function argument <tt>Term</tt>s of this <tt>Term</tt> and returns true,
     * if one of the function arguments contains <tt>t</tt>.<br>
     * This method was included to support ite-constructs.
     * 
     * @param f the <tt>Formula</tt> to be checked for containment in this <tt>Term</tt>
     * @return true if this <tt>Term</tt> contains f
     */
    public boolean containsFormulaIteTerm( Formula f ) {
        for ( int i = 0; i < funcArgs.length; i++ ) {
            if ( funcArgs[i].containsFormulaIteTerm( f ) ) return true;            
        }
        return false;
    }
        
     
    /** Compares this <tt>Term</tt> to the specified <tt>Object</tt>.
     * <p>
     * This implementation tries to determine equality by first checking if <tt>o</tt> is an
     * instance of <tt>Term</tt>. If so, it checks if the function name of <tt>o</tt> is equal to
     * the function name of this <tt>Term</tt>. If true, it checks if all function argument
     * <tt>Term</tt>s contained in this <tt>Term</tt> are equal to those contained in <tt>o</tt>,
     * and in same order. If so, true is returned.  
     * <p>
     * Overriding methods are recommended to check for object equality in addition; this is not
     * done in this implementation.
     * 
     * @param o the <tt>Object</tt> to compare with
     * @return true if this <tt>Term</tt> is the same as the <tt>Object</tt> o; otherwise false.
     */
    public boolean equals( Object o ) {
        if ( o instanceof Term ) {
            Term t = ( Term ) o;
            if ( function.equals( t.getFunction() ) ) {                                          
                Term[] tFuncArgs = t.getFuncArgs();
                if ( funcArgs.length == tFuncArgs.length ) {
                    for ( int i = 0; i < funcArgs.length; i++ ) {
                        if ( ! funcArgs[i].equals( tFuncArgs[i] ) ) return false;
                    }
                    return true;
                }
            }
        }
        return false;    
    }
    
    
    /** Returns an int value representing the hash code of this <tt>Term</tt>. 
     * <p>
     * The hash code for a <tt>Term</tt> is calculated during its creation. This is done by
     * combining the hash code of its function name with the hash codes of its function
     * arguments, if available, to a new hash code. The order of function arguments matters for
     * this implementation
     * 
     * @return the hashCode of this <tt>Term</tt>
     */
    public int hashCode() {
        return hashCode; 
    }
     

    /** Returns a String representation of this <tt>Term</tt>, containing the String representation
     * of each of its arguments.
     * <p>
     * The returning <tt>String</tt> is formatted and can be parsed according to the SMT-Lib
     * grammar specification (chapter seven, "Concrete Syntax") 
     * 
     * @see <a href="http://combination.cs.uiowa.edu/smtlib/papers/format-v1.1-r05.04.12.pdf">
     *      The SMT-LIB Standard: Version 1.1</a> 
     * 
     * @return a String representation of this <tt>Term</tt>
     */
    public abstract String toString();

    
    /** Replaces all occurrences of a specified <tt>TermVariable</tt> by a specified <tt>Term</tt> 
     * in a this <tt>Term</tt>.
     * <p>
     * Thereby this <tt>Term</tt> and the returned replaced <tt>Term</tt> share the same objects
     * in their fields, except for those objects which contained the specified 
     * <tt>TermVariable</tt>.<br>
     * This implicates that if <tt>termVar</tt> is not contained in this <tt>Term</tt>,
     * this <tt>Term</tt> is returned without changes.
     * 
     * @param termVar the <tt>TermVariable</tt> to be replaced
     * @param replacement the <tt>Term</tt> used to replace termVar
     * @return the <tt>Term</tt> obtained by replacing every (free) occurence of termVar by 
     *         replacement in this <tt>Term</tt>
     */
    public abstract Term replaceTermVar( TermVariable termVar, Term replacement );
    

    /** Replaces all occurrences of a specified <tt>FormulaVariable</tt> by a specified 
     * <tt>Formula</tt> in a this <tt>Term</tt>.
     * <p>
     * Thereby this <tt>Term</tt> and the returned replaced <tt>Term</tt> share the same objects
     * in their fields, except for those objects which contained the specified 
     * <tt>FormulaVariable</tt>.<br>
     * This implicates that if <tt>formVar</tt> is not contained in this <tt>Term</tt>,
     * this <tt>Term</tt> is returned without changes.
     * <p>
     * This method was included to support ite-constructs
     *  
     * @param formVar the <tt>FormulaVariable</tt> to be replaced
     * @param replacement the <tt>Formula</tt> used to replace formVar
     * @return the <tt>Term</tt> obtained by replacing every (free) occurence of formVar by
     *         replacement in this <tt>Term</tt>
     */
    public abstract Term replaceFormVarIteTerm( FormulaVariable formVar, Formula replacement );    
     
    
    
    /* Internal (protected) methods */
    
    /** Determines if a given identifier represents a legal identifier symbol in QF_AUFLIA.
     * <p>
     * An identifier is legal if it begins with a letter and consists only of letters, digits and
     * the characters '.' , '_' and ''' (single quotation mark)
     * 
     * @param identifier the String to be checked
     * @return true if the specified String represents a legal identifier symbol; otherwise false
     * 
     * @throws NullPointerException if <tt>identifier</tt> is null
     */
    protected static final boolean isLegalIdentifier( String identifier ) {
        char first = identifier.charAt( 0 ); 
        // First character must be a letter
        if ( ( first >= 'A'  &&  first <= 'Z' )  ||  ( first >= 'a'  &&   first <= 'z' ) ) {
            char act;
            // All other characters must be letters or digits or '.', '_' or "'"
            for( int i = 1; i < identifier.length(); i++ ) {
                act = identifier.charAt( i );
                if ( ! ( ( act >= 'A'  &&  act <= 'Z' )  ||  ( act >= 'a'  &&   act <= 'z' )  ||
                       ( act >= '0'  &&  act <= '9' )  ||  
                       ( act == '.'  ||  act == '_'  ||  act == '\'' ) ) 
                    ) return false;
            }
            return true;
        }
        return false;
    }   
}
