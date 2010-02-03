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
//                Universitaet Koblenz-Landau, Germany
//                Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.decproc.smtlib;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.proof.decproc.DecisionProcedureSmtAufliaOp;


/** Represents a signature for the uninterpreted terms and formulae of the SMT-Lib specification
 * and the QF_AUFLIA sublogic.
 * <p>
 * A signature thereby is a <tt>String</tt> array, with each <tt>String</tt> representing the 
 * required sort for the corresponding argument and the result sort of an uninterpreted
 * function respectively.
 * <p> 
 * A <tt>Signature</tt> is immutable, i.e. after creation its attribute values cannot be altered
 * any more . Due to this immutability, it is possible to cache the created signature objects 
 * internally to reduce memory footprint  
 * 
 * @author akuwertz
 * @version 1.2,  12/05/2005  (Replaced exception by standard exceptions; added further comments)                   
 */

public final class Signature {
    
    /* Additional fields */
    
    /** The array of signature symbols of this <tt>Signature</tt> */
    private final String[] signature;
    /** The set of uninterpreted sort symbols of this <tt>Signature</tt> */
    private final Set uiSorts;
    /** The cached hash code of this <tt>Signature</tt> */
    private final int hashCode;
    /** Cached <tt>Signature</tt> object representing a one symbol signature */
    private static Signature oneIntSig, oneArrSig;
    /** Cache for <tt>Signature</tt> objects which only consist of integer symbols */
    private static final HashMap intSigs = new HashMap();
    
    
    /* String constants for failures during Signature creation */
    private static final String creationFailureSigNull = "Signature symbol array is null!"; 
    private static final String 
        creationFailureSigContNull = "Signature symbol array contains a nullpointer at position !";
    private static final String creationFailureArityNegative = "Arity must not be negative!";
    
    
    
    /* Constructors */
    
    /** Creates a new <tt>Signature</tt>, which consists of the specified <tt>String</tt>s
     * 
     * @param sig the array of signature symbols for this <tt>Signature</tt>
     * @throws NullPointerException if <tt>sig</tt> is or contains any nullpointer
     */
    public Signature( String[] sig ) {
        if ( sig == null ) throw new NullPointerException( creationFailureSigNull );       
        signature = ( String[] ) sig.clone();
        uiSorts = findUiSorts(); // Also checks for null pointer
        int result = 17;
        for ( int i = 0; i < sig.length; i++ ) {
            result = 37*result + sig[i].hashCode();    
        }
        hashCode = result; 
    }
    
    
    
    /*  Public method implementation */
    
    /** A factory method that returns a <tt>Signature</tt> instance which consists only of 
     * symbols representing integers in QF_AUFLIA.  
     * <p>
     * Because <tt>Signature</tt>s can be assigned to functions and predicates, there is a
     * parameter 'hasReturnType' indicating if the return type of the assigned object should
     * be contained in this <tt>Signature</tt> (This is the case for uninterpreted function,
     * but not for uninterpreted predicates ).
     * <p>
     * The <tt>Signature</tt> objects returned by this method are cached internally. Therefore
     * on successive calls with same or equivalent arguments this method provides same objects.
     * Arguments are considered equivalent if they result in <tt>Signatures</tt> of the same length.
     * This cache is provided to reduce memory footprint. It can be cleared by calling the 
     * <tt>clearSignatureCache</tt> method.
     *  
     *  
     * @param arity the arity of the function/predicate symbol which the <tt>Signature</tt>
     *              is to be assigned to
     * @param hasReturnType Specifies if an integer symbol should be added at the end of the
     *                      returned <tt>Signature</tt>, representing the return type of its
     *                      assigned function 
     * @return a <tt>Signature</tt> consisting of the specified number of integer symbols
     * 
     * @throws IllegalArgumentException if <tt>arity</tt> is negative
     * 
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Signature#clearSignatureCache() 
     */
    public static Signature intSignature( int arity, boolean hasReturnType ) {
        if ( arity < 0 ) throw new IllegalArgumentException( creationFailureArityNegative );
        // If there is a return type, the signature consists of arity + 1 'ints'
        int count = hasReturnType ? arity + 1 : arity;
        Integer index = new Integer( count );        
        if ( intSigs.get( index ) == null ) {
            String[] ints = new String[ count ];
            for ( int i = 0; i < count; i++ ) {
                ints[i] = DecisionProcedureSmtAufliaOp.INT;             
            }
            intSigs.put( index , new Signature( ints ) );
        }
        return ( Signature ) intSigs.get( index );        
    }
    
    
    /** A factory method that returns a <tt>Signature</tt> instance which consists of only one
     * symbol representing an array or an integer in QF_AUFLIA.
     * <p>
     * The objects returned by this method are cached internally. Therefore successive calls with
     * the same value for <tt>switcher</tt> return the same objects.<br>
     * This cache is provided to reduce memory footprint.
     *   
     * @param switcher a boolean used to decide if the signature symbol should be the array (true)
     *                 or the integer symbol (false)  
     * @return a <tt>Signature</tt> consisting of only one symbol   
     */
    public static Signature constSignature( boolean switcher ) {
        if ( switcher ) {
            if ( oneArrSig == null ) {
                oneArrSig = new Signature( new String[]{ DecisionProcedureSmtAufliaOp.ARRAY } );
            }    
            return oneArrSig;
        }
        if ( oneIntSig == null ) {
            oneIntSig = new Signature( new String[]{ DecisionProcedureSmtAufliaOp.INT } );
        }    
        return oneIntSig;                
    }
    
    
    
    
    /** Returns an array containing the signature symbols of this <tt>Signature</tt> as shallow copy
     *  
     * @return the array of signature symbols for this <tt>Signature</tt> 
     */
    public String[] getSymbols() {        
        return ( String[] ) signature.clone();
    }
    
    
    /** Returns the length of this <tt>Signature</tt>, i.e. the the number of signature symbols
     * contained in this <tt>Signature</tt>.
     * 
     * @return the length of this <tt>Signature</tt>
     */
    public int getLength() {
        return signature.length;
    }
    
    
    /** Return an array of all uninterpreted sort symbols contained in this <tt>Signature</tt>
     * as shallow copy
     * 
     * @return the array of all uninterpreted sort symbols of this <tt>Signature</tt>
     */
    public Set getUiSorts() {
        return new HashSet( uiSorts ); 
    }
    
    
    /** Compares this <tt>Signature</tt> to the specified <tt>Object</tt>.
     * <p>
     * <tt>o</tt> is equal to this <tt>Signature</tt> if it is an instance of <tt>Signature</tt>
     * and if the <tt>String</tt> array containing the signature symbols of this <tt>Signature</tt>
     * is equal to that of <tt>o</tt>
     * 
     * @return true iff the specified <tt>Object</tt> is equals to this <tt>Signature</tt>
     */
    public boolean equals( Object o ) {
        if ( o == this ) return true;
        if ( o instanceof Signature ) {
            Signature sig = ( Signature ) o;
            if ( signature.length ==  sig.getLength() ) {
                String[] sigSig = sig.getSymbols();
                for ( int i = 0; i < signature.length; i++ ) {
                    if ( ! signature[i].equals( sigSig[i] ) ) return false;
                }
                return true;
            }
            
        }
        return false;
    }
    
    
    /** Returns an int value representing the hash code of this <tt>Signature</tt>. 
     * <p>
     * The hash code for a <tt>Signature</tt> is calculated during its creation by combining
     * the hash codes of its signature symbols to a new one
     * 
     * @return the hash Code of this <tt>Signature</tt>
     */
    public int hashCode() {
        return hashCode;
    }
    
    
    /** Returns a string representation of this <tt>Signature</tt>.
     * <p>
     * The returned <tt>String</tt> consists of the signature symbols, separated by spaces
     * 
     * @return the string representation of this <tt>Signature</tt> 
     */
    public String toString() {
        if ( signature.length == 0 ) return "";
        String out = signature[0];
        for (int i = 1; i < signature.length; i++ ) {
            out += " " + signature[i]; 
        }
        return out;
    }
    
    
    /** Clears the cache for <tt>Signature</tt> objects created with the <tt>intSignature</tt>
     * method 
     * 
     * @see de.uka.ilkd.key.proof.decproc.smtlib.Signature#intSignature(int, boolean)
     */
    public static void clearSignatureCache() {
        intSigs.clear();
    }
    
    
    
    // Internal methods
    
    /** Finds all uninterpreted sort symbols contained in this <tt>Signature</tt>, and returns
     * them as a <tt>Set</tt>
     * 
     * @return a <tt>Set</tt> of all uninterpreted sort symbols contained in this <tt>Signature</tt>
     */
    private Set findUiSorts() { 
        Set foundUiSorts = new HashSet();
        String toTest;
        for ( int i = 0; i < signature.length; i++ ) {
            toTest = signature[i];
            if ( toTest == null ) throw new NullPointerException( creationFailureSigContNull + i );
            if (  toTest != DecisionProcedureSmtAufliaOp.INT  
                & toTest != DecisionProcedureSmtAufliaOp.ARRAY ) {
                foundUiSorts.add( toTest );
            }
        }
        return foundUiSorts;        
    }
}
