// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
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

/** Represents a formula as defined in the SMT-Lib specification, and specialized in one of the
 * AUFLIA sublogics. These are QF_AUFLIA and AUFLIA, whereas QF_AUFLIA is the quantifier free
 * version of AUFLIA. Thereby a formula represents an object which can be assigned a truth
 * value, i.e. one predicate or many logical connected predicates. 
 * <p>
 * This class is abstract because it is intended as a frame for realizing subclasses which 
 * specialize in representing one class of predicates in (QF_)-AUFLIA (e.g. uninterpreted predicates).
 * <p>
 * Formulae are immutable; their attribute values cannot be changed after they are created. 
 * <p>
 * This class also contains methods with protected access intended to be used by realizing 
 * subclasses for convenience, as well as methods to access the lists of all uninterpreted functions
 * and predicates contained in this formula, which are provided for the simple integration of terms
 * and formulae and into benchmarks.
 * 
 * @author akuwertz
 * 
 * @version 1.5,  12/06/2005  (Restructuring and further commenting)
 * 
 * @see <a href="http://goedel.cs.uiowa.edu/smtlib/logics/QF_AUFLIA.smt">QF_AUFLIA</a>
 * @see <a href="http://goedel.cs.uiowa.edu/smtlib/logics/AUFLIA.smt">AUFLIA</a>
 * @see <a href="http://goedel.cs.uiowa.edu/smtlib">SMT-LIB</a>
 */

public abstract class Formula {
    
    /** The top-level operator of this <tt>Formula</tt> */ 
    private final String op;
    
    /** The array of subformulae of this <tt>Formula</tt> */
    private final Formula[] subformulae;
    
    /** A template <tt>Fomula</tt> array assigned to <tt>subformulae</tt> if this <tt>Formula</tt> has no
     * subformulae. This shared object is intended to lower memory footprint */       
    private static final Formula[] emptySubformulae = new Formula[0];
    
    /** The array of subterms of this <tt>Formula</tt> */
    private final Term[] subterms;
    
    /** A template <tt>Term</tt> array assigned to <tt>subterms</tt> if this <tt>Formula</tt> has no
     * subterms. This shared object is intended to lower memory footprint */       
    private static final Term[] emptySubterms = new Term[0];
    
    /** The <tt>Vector</tt> of all uninterpreted functions contained in this <tt>Formula</tt> */
    private final Vector uninterFuncs;
    
    /** The <tt>Vector</tt> of all uninterpreted predicates contained in this <tt>Formula</tt> */
    private final Vector uninterPreds;
    
    /** A template <tt>Vector</tt> assigned to the <tt>Formula</tt> attributes which store the
     * uninterpreted functions and predicates of this <tt>Formula</tt>, if these fields are empty.
     * This shared object is intended to lower memory footprint */      
    private static final Vector emptyVector = new Vector();
    
    /** The cached hash code for this <tt>Formula</tt> */     
    private final int hashCode;
    
    
    
    /* Constructor */
    
    /** Sole constructor. For invocation by constructors of realizing subclasses.
     * <p>
     * This explicit constructor sets the internal fields to the specified values or rather to
     * values computed out of the given ones. Thereby the top-level operator and the subformulae
     * and subterms are set directly, whereby the <tt>Vector</tt> of uninterpreted predicates and
     * functions respectively are computed out of the uninterpreted predicates and functions
     * contained in the subformulae and subterms.<br> 
     * Therefor all <tt>Formula</tt>e and <tt>Term</tt>s contained as subelements are searched for
     * uninterpreted predicates (and functions respectively) and the results are merged into a 
     * <tt>Vector</tt>, eleminating duplicate entries.<br>
     * The <tt>boolean</tt> <tt>addThisUip</tt> is a flag serving as indicator to the constructor
     * that the calling subclass instance also wishes to be added to the <tt>Vector</tt> of
     * uninterpreted predicates. If it is set to <tt>true</tt>, the calling instance will be 
     * added to the <tt>Vector</tt> of uninterpreted predicates as its first element.
     * <p> 
     * This implementation checks for null pointers in the specified arguments. If a null pointer
     * is found in the top-level operator <tt>op</tt>, all fields will be set to <tt>null</tt>
     * without throwing any exceptions. This is done to enable realizing subclasses to throw
     * specific exceptions on their part. It implicates that every subclass realizing this class
     * must check <tt>op</tt> for being a null pointer, and, if so, throw an exception. Otherwise
     * the methods defined in this class could fail with a <tt>NullPointerException</tt>, if called
     * on the created subclass instance.<br>
     * The same holds for the <tt>Formula</tt>e and <tt>Term</tt>s contained in the subformulae and
     * subterms arrays. If one of the specified arrays contains any null pointers, all fields of 
     * this <tt>Formula</tt> instance will become undefined, without throwing an exception.
     * Realizing subclasses therefore have to check or ensure that <tt>forms</tt> and 
     * <tt>terms</tt> contain no null pointers; otherwise the methods defined in this class could
     * fail with a <tt>NullPointerException</tt>.<br>
     * In contrary to this, null pointers are allowed for the array objects theirselves. This is done for
     * convenience and has to same effects as empty arrays would have.
     * 
     * @param operator the top-level operator of this <tt>Formula</tt> 
     * @param forms the array of subformulae for this <tt>Formula</tt>
     * @param terms the array of subterms for this <tt>Formula</tt>
     * @param addThisUip a flag; if set to <tt>true</tt>, the calling subclass instance will be
     *                   added the to uninterpreted predicate <tt>Vector</tt> of this <tt>Formula</tt>
     */
    protected Formula( String operator, Formula[] forms, Term[] terms, boolean addThisUip ) {
        
        if ( operator == null ) {
            op = null;
            subformulae = null;
            subterms = null;
            uninterFuncs = uninterPreds = null;
            hashCode = 0;
            // Handling of this null pointer situation has to be done by subclass
            return;
        }
        op = operator;
        
        // Null pointer for forms or terms is allowed for convenience
        // Given arrays are cloned for immutability (exclusiveness)
        if ( forms == null  ||  forms.length == 0 ) subformulae = emptySubformulae;  
        else subformulae = ( Formula [] ) forms.clone();
        if ( terms == null  ||  terms.length == 0 ) subterms = emptySubterms;  
        else subterms = ( Term [] ) terms.clone();
                        
        // Estimate capacity of new uif and uip Vectors to reduce reallocation effects to one
        int estSizeUip = 0, estSizeUif = 0;
        Vector[] uipInSubforms = new Vector[ subformulae.length ];
        Vector[] uifInSubforms = new Vector[ subformulae.length ];
        Vector[] uipInSubterms = new Vector[ subterms.length ];
        Vector[] uifInSubterms = new Vector[ subterms.length ];

        try {
            for ( int i = 0; i < subformulae.length; i++ ) {
                uipInSubforms[i] = subformulae[i].getUIPredicates();
                uifInSubforms[i] = subformulae[i].getUIF();                                
                estSizeUip += uipInSubforms[i].size();
                estSizeUif += uifInSubforms[i].size();
            }
            for ( int i = 0; i < subterms.length; i++ ) {
                uipInSubterms[i] = subterms[i].getUIPredicatesIteTerm();
                uifInSubterms[i] = subterms[i].getUIF();
                estSizeUip += uipInSubterms[i].size();                
                estSizeUif += uifInSubterms[i].size();
            }
        } catch ( NullPointerException e ) {
            uninterFuncs = uninterPreds = null;
            hashCode = 0;
            // Handling of this null pointer situation has to be done by subclass
            return;
        }
        
        // Compute Vector of uninterpreted predicates contained in this Formula
        if ( ! addThisUip && estSizeUip == 0 ) { 
            // If no uninterpreted predicates contained, use empty template Vector
            uninterPreds = emptyVector;
        } else {
            // Create new Vector of appropriate size and prepare the HashSet for function names
            HashSet contPredNames = new HashSet( estSizeUip + 1 );
            Vector addUips;
            if ( ! addThisUip ) addUips = new Vector( estSizeUip );
            //  If addThisUip is true, make sure uninterPreds contains a refenrence to itself
            else {
                addUips = new Vector( estSizeUip + 1);
                addUips.add( this );
                contPredNames.add( op );
            }
            // Compute contained ui predicates
            Vector uipVector;
            for ( int i = 0; i < uipInSubforms.length; i++ ) {
                uipVector = uipInSubforms[i];
                for( int j = 0; j < uipVector.size(); j++ ) {
                    if ( contPredNames.add( ( ( Formula ) uipVector.get(j) ).getOp() ) ) {
                        addUips.add( uipVector.get(j) );
                    }
                }
            }
            for ( int i = 0; i < uipInSubterms.length; i++ ) {
                uipVector = uipInSubterms[i];
                for( int j = 0; j < uipVector.size(); j++ ) {
                    if ( contPredNames.add( ( ( Formula ) uipVector.get(j) ).getOp() ) ) {
                        addUips.add( uipVector.get(j) );
                    }
                }
            }
            addUips.trimToSize();
            uninterPreds = addUips;            
        }
        
        // Compute Vector of uninterpreted functions contained in this Formula
        if ( estSizeUif == 0 ) { 
            // If no uninterpreted functions contained, use empty template Vector
            uninterFuncs = emptyVector;
        } else {
            // Compute Vector lengths and Vector elements, i.e. uninterpreted functions
            HashSet contFuncNames = new HashSet( estSizeUif );
            // Create new Vector of estimated capacity
            Vector addUifs = new Vector( estSizeUif );
            // Compute contained ui functions
            Vector uifVector;
            for ( int i = 0; i < uifInSubforms.length; i++ ) {
              uifVector = uifInSubforms[i];
                for( int j = 0; j < uifVector.size(); j++ ) {
                    if ( contFuncNames.add( ( ( Term ) uifVector.get(j) ).getFunction() ) ) {
                        addUifs.add( uifVector.get(j) );
                    }
                }
            }
            for ( int i = 0; i < uifInSubterms.length; i++ ) {
              uifVector = uifInSubterms[i];
                for( int j = 0; j < uifVector.size(); j++ ) {
                    if ( contFuncNames.add( ( ( Term ) uifVector.get(j) ).getFunction() ) ) {
                        addUifs.add( uifVector.get(j) );
                    }
                }
            }
            addUifs.trimToSize();
            uninterFuncs = addUifs;
        }
        
        // Calculate hash code for this Formula
        int result = 17;
        result = 37*result + op.hashCode();
        for ( int i = 0; i < subformulae.length; i++ ) {
            result = 37*result + subformulae[i].hashCode();
        }
        for ( int i = 0; i < subterms.length; i++ ) {
            result = 37*result + subterms[i].hashCode();
        }        
        hashCode = result;
    }
    
    
    /** Sole constructor; added for convenience.
     * <p>
     * Represents only a shorter form of the general constructor, with <tt>addThisUip</tt> 
     * set to <tt>false</tt> by default.
     * 
     * @param operator the top-level operator of this <tt>Formula</tt> 
     * @param forms the array of subformulae for this <tt>Formula</tt>
     * @param terms the array of subterms for this <tt>Formula</tt>
     * 
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Formula#Formula(String, Formula[], Term[], boolean)
     */
    protected Formula( String operator, Formula[] forms, Term[] terms ) {
        this( operator, forms, terms, false );
    }
 
    

    /* Now the public methods and, supplemental, the protected setters */
    
    /** Returns the top-level operator of this <tt>Formula</tt>
     * 
     * @return the top-level operator of this <tt>Formula</tt>
     */
    public final String getOp() {
        return op;
    }
    
    
    /** Returns a shallow copy of the subformulae array of this <tt>Formula</tt> 
     *  
     * @return the array of subformulae of this <tt>Formula</tt> 
     */    
    public final Formula[] getSubformulae() {
        return ( Formula[] ) subformulae.clone();
    }
    
    
    /** Returns a shallow copy of the subterms array of this <tt>Formula</tt>
     * 
     * @return the array of subterms of this <tt>Formula</tt> 
     */    
    public final Term[] getSubterms() {
        return ( Term[] ) subterms.clone();
        
    }
    
    
    /** Returns a <tt>Vector</tt> of all uninterpreted predicates contained in this <tt>Formula</tt>
     * 
     * @return a <tt>Vector</tt> of all uninterpreted predicates contained in this <tt>Formula</tt>
     */
    public final Vector getUIPredicates() {        
        return ( Vector ) uninterPreds.clone();
    }
    
    
    /** Returns a <tt>Vector</tt> of all uninterpreted functions contained in this <tt>Formula</tt>
     * as a shallow copy
     * 
     * @return a <tt>Vector</tt> of all uninterpreted functions contained in this <tt>Formula</tt>
     */
    public final Vector getUIF() {
        return ( Vector ) uninterFuncs.clone();                
    }
    
    
    /** Returns true if this <tt>Formula</tt> contains <tt>f</tt> as a subformula.
     * <p>
     * This implementation tries to determine containment by first checking if <tt>f</tt> 
     * <tt>equals</tt> this <tt>Formula</tt>. If not, it calls <tt>containsFormula</tt> recursively
     * first on the subformulae of this <tt>Formula</tt>, then on its subterms, returning 
     * <tt>true</tt> if one of these subelements contains <tt>f</tt>
     * <p>
     * If this method is called on an <tt>FletFormula</tt> with the <tt>FormulaVariable</tt>
     * which will be semantically replaced in the <tt>FletFormula</tt> as argument, it will
     * only check the replaced <tt>Formula</tt> for occurences of <tt>f</tt>
     * 
     * @param f the <tt>Formula</tt> to be checked for containment in this <tt>Formula</tt>
     * @return true if this <tt>Formula</tt> contains f
     * 
     * @see FletFormula#containsFormula(Formula)
     */
    public boolean containsFormula( Formula f ) {
        if ( equals ( f ) ) return true;
        for ( int i = 0; i < subformulae.length; i++ ) {
            if ( subformulae[i].containsFormula( f ) ) return true;
        }
        for ( int i = 0; i < subterms.length; i++ ) {
            if ( subterms[i].containsFormulaIteTerm( f ) ) return true;
        }
        return false;
    }
    
    
    /** Returns true if this <tt>Formula</tt> contains the <tt>Term</tt> <tt>t</tt>.
     * <p>
     * This implementation tries to determine containment recursively by calling
     * <tt>containsTerm</tt> first on the subformulae of this <tt>Formula</tt>, then on its
     * subterms, returning <tt>true</tt> if one of these subelements contains <tt>t</tt>.
     * <p>
     * If <tt>t</tt> is a <tt>TermVariable</tt>, this method will only check for free 
     * term variables, i.e. if this method is called on a <tt>QuantifierFormula</tt> or a 
     * <tt>LetFormula</tt> with the quantified or rather bound <tt>TermVariable</tt> as argument,
     * it will return <tt>false</tt>
     *   
     * @param t the <tt>Term</tt> to be checked for containment in this <tt>Formula</tt>
     * @return true if this <tt>Formula</tt> contains t
     * 
     * @see QuantifierFormula#containsTerm(Term)
     * @see LetFormula#containsTerm(Term)
     */
    public boolean containsTerm( Term t ) {
        for ( int i = 0; i < subformulae.length; i++ ) {
            if ( subformulae[i].containsTerm( t ) ) return true;
        }
        for ( int i = 0; i < subterms.length; i++ ) {
            if ( subterms[i].containsTerm( t ) ) return true;
        }
        return false;
    }
    
    
    /** Compares this <tt>Formula</tt> to the specified <tt>Object</tt> <tt>o</tt>.
     * <p>
     * This implementation tries to determine equality by first checking if <tt>o</tt> is an instance
     * of <tt>Formula</tt>. If so, it checks if the top-level operator of <tt>o</tt> is equal to that
     * of this <tt>Formula</tt>. If true, it checks if all subformulae and subterms contained in this
     * <tt>Formula</tt> are equal to those contained in <tt>o</tt>, and in the same order. If all these
     * constraints are satisfied, true is returned. 
     * <p>
     * Overriding methods are recommended to check for object equality in addition; this is not done in
     * this implementation.
     * 
     * @param o the <tt>Object</tt> to compare with
     * @return true if this <tt>Formula</tt> is the same as the specified <tt>Object</tt>;
     *         otherwise false.
     */  
    public boolean equals( Object o ) {
        if ( o instanceof Formula ) {
            Formula f = ( Formula ) o;
            if ( op.equals( f.getOp() ) ) {
                if ( subformulae.length == f.getSubformulae().length ) {
                    if ( subterms.length == f.getSubterms().length ) {
                        Formula[] fSubformulae = f.getSubformulae();
                        Term[] fSubterms = f.getSubterms();
                        for ( int i = 0; i < subformulae.length; i++ ) {
                            if ( ! subformulae[i].equals( fSubformulae[i] ) ) 
                                return false;
                        }            
                        for ( int i = 0; i < subterms.length; i++ ) {
                            if ( ! subterms[i].equals( fSubterms[i] ) ) 
                                return false;
                        }
                        return true;
                    }
                }    
            }
        }
        return false;
    }
    
    
    /** Returns an int value representing the hash code of this <tt>Formula</tt>. 
     * <p>
     * The hash code for a <tt>Formula</tt> is calculated during its creation. This is done by
     * combining the hash code of its operator with the hash codes of, if available, its subformulae
     * and its subterms to a new hash code. The order of subformulae and subterms matters for this 
     * implementation
     * 
     * @return the hashCode of this <tt>Term</tt>
     */
    public int hashCode() {
        return hashCode; 
    }
    
    
    /** Returns a String representation of this <tt>Formula</tt>, containing the String 
     * representation of each of its subformulae and/or subterms. The returned <tt>String</tt>
     * is formatted and can be parsed according to the SMT-Lib grammar specification (chapter seven,
     * "Concrete Syntax"). 
     * 
     * @see <a href="http://combination.cs.uiowa.edu/smtlib/papers/format-v1.1-r05.04.12.pdf">
     *      The SMT-LIB Standard: Version 1.1</a>    
     * 
     * @return a String representation of this <tt>Formula</tt>
     */
    public abstract String toString();
    
    
    /** Replaces all occurrences of a specified <tt>FormulaVariable</tt> by a specified
     * <tt>Formula</tt> in a this <tt>Formula</tt>.
     * <p>
     * Thereby this <tt>Formula</tt> and the returned replaced <tt>Formula</tt> share the
     * same objects in their fields, except for those objects which contained the
     * specified <tt>FormulaVariable</tt>.<br>
     * This implicates that if <tt>formVar</tt> is not contained in this <tt>Formula</tt>,
     * this <tt>Formula</tt> is returned without changes.
     *   
     * @param formVar the <tt>FormulaVariable</tt> to be replaced
     * @param replacement the <tt>Formula</tt> used to replace formVar
     * @return the <tt>Formula</tt> obtained by replacing every (free) occurence of formVar
     *         by replacement in this <tt>Formula</tt>  
     */
    public abstract Formula replaceFormVar( FormulaVariable formVar, Formula replacement );
    
    
    /** Replaces all occurrences of a specified <tt>TermVariable</tt> by a specified <tt>Term</tt> 
     * in a this <tt>Formula</tt>.
     * <p>
     * Thereby this <tt>Formula</tt> and the returned replaced <tt>Formula</tt> share the
     * same objects in their fields, except for those objects which contained the
     * specified <tt>TermVariable</tt>.<br>
     * This implicates that if <tt>termVar</tt> is not contained in this <tt>Formula</tt>,
     * this <tt>Formula</tt> is returned without changes.
     *  
     * @param termVar the <tt>TermVariable</tt> to be replaced
     * @param replacement the <tt>Term</tt> used to replace termVar
     * @return the <tt>Formula</tt> obtained by replacing every (free) occurence of termVar
     *         by replacement in this <tt>Formula</tt>
     */
    public abstract Formula replaceTermVar( TermVariable termVar, Term replacement );
    
    
    
    // Further internal (protected) methods
            
    /** Converts an array into a <tt>Vector</tt>, preserving element order
     *  
     * @param objects The array which should be converted into a <tt>Vector</tt> 
     * @return a <tt>Vector</tt> containing all the <tt>Object</tt>s in the specified array,
     *         in the same order
     */
    protected static final Vector toVector( Object[] objects ) {
        Vector vector = new Vector( objects.length );
        for ( int i = 0; i < objects.length; i++ ) {
            vector.add( i, objects[i] );
        }
        return vector;
    }
    
   
    /** Determines if a given identifier represents a legal identifier symbol in (QF_)AUFLIA.
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
