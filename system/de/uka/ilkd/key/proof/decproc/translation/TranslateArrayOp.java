// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.decproc.translation;

import org.apache.log4j.Logger;
import de.uka.ilkd.key.logic.op.ArrayOp;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.ObjectSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.decproc.smtlib.*;

/** This class represents the translation rule for <tt>ArrayOp</tt>s.
 * <p>
 * Thereby the array access represented by the <tt>ArrayOp</tt> is translated into an SMT-LIB 
 * <tt>UninterpretedFuncTerm</tt>, if the array is of <tt>Sort</tt> INT or OBJECT. If it is of 
 * boolean <tt>Sort</tt>, it is translated into an SMT-LIB <tt>UninterpretedPredFormula</tt>.<br>
 * The created functions or predicates consist of two arguments: their first argument represents the
 * accessed array itself, and the second argument specifies the index to be accessed
 * <p>
 *  
 * @author akuwertz
 * @version 1.3,  12/13/2006  (Minor fixes for AUFLIA support)
 */

public class TranslateArrayOp implements IOperatorTranslation {

    /* Additional fields */
           
    /** A prefix used in the names of the uninterpreted functions and predicates respectively to
     * indicate that they represent a translation of an <tt>ArrayOp</tt> */
    private static final String arrayOpPrefix = "Array";
    
    /** A suffix used in the name of the created uninterpreted function to mark it as function */
    private static final String arrayOpUifSuffix = "_UIF";
    /** A suffix used in the name of the created uninterpreted predicate to mark it as predicate */
    private static final String arrayOpUipSuffix = "_UIP";
    
    /** A suffix used in the name of the created uninterpreted function to indicate that it 
     * represents the translation of an integer attribute */
    private static final String arrayOpIntSuffix = "_int";
    
    /** A <tt>Logger</tt> for logging and debugging operator translation */
    private static final Logger logger = Logger.getLogger( TranslateArrayOp.class.getName() );
        // Logger is created hierarchical to inherit configuration and behaviour from parent
        
    /* String constants for error messages */
    private static final String translationFailure = 
        "Translation of array operator failed due to illegal arguments on visitor stack:\n";
    private static final String failureCause = 
        " expected an argument of class Term (SMT-LIB) and found the object:\n";
    private static final String failureCauseNoFuncTerm = 
        " expected an argument of class UninterpretedFuncTerm (SMT-LIB) and found the object:\n";
    private static final String unsupportedArrayOp =
        "Translation of array op failed because its element sort could not be handled by this class: ";
    
    
    
    /* Public method implementation */
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.translation.IOperatorTranslation#isApplicable(de.uka.ilkd.key.logic.op.Operator)
     */
    public boolean isApplicable( Operator op ) {
        return op instanceof ArrayOp;
    }

    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.translation.IOperatorTranslation#translate(de.uka.ilkd.key.logic.op.Operator, de.uka.ilkd.key.proof.decproc.translation.TermTranslationVisitor)
     */
    public Object translate(Operator op, TermTranslationVisitor ttVisitor) {
        
        logger.debug( "Popping two argument terms from stack" );
        Object[] args = ttVisitor.getTranslatedArguments( 2 );
        Term[] convArgs;
        
        Sort elementSort = ( (ArraySort) ((ArrayOp) op).arraySort() ).elementSort();
        Sort integerSort = ttVisitor.getServices().getTypeConverter().getIntegerLDT().targetSort();
        Sort booleanSort = ttVisitor.getServices().getTypeConverter().getBooleanLDT().targetSort();
        Signature uiSig;
        
        // The first argument represents the array itself
        if ( ! ( args[0] instanceof UninterpretedFuncTerm  || args[0] instanceof TermVariable ) ) {
            throw new IllegalArgumentException ( 
                translationFailure + op.name() + failureCauseNoFuncTerm + args[0] );
        }    
        
        // The second argument represents the index of the accessed element
        if ( ! ( args[1] instanceof Term ) ) throw new IllegalArgumentException
            ( translationFailure + op.name() + failureCause + args[1] ); 
        
        convArgs = new Term[]{ (Term) args[0], (Term) args[1] };

        // The integer array case:
        if ( elementSort.extendsTrans( integerSort ) ) {
            logger.info( "Found integer array, creating uninterpreted function" );
            uiSig = Signature.intSignature( 2 , true );
            String funcName = arrayOpPrefix + arrayOpUifSuffix + arrayOpIntSuffix;
            ttVisitor.createTypePredUif( elementSort, funcName, 2 );
            return new UninterpretedFuncTerm( funcName, convArgs, uiSig );
        }

        // The object array case:
        if ( elementSort instanceof ObjectSort ) {
            logger.info( "Found object array, creating uninterpreted function" );
            uiSig = Signature.intSignature( 2 , true );
            String funcName = arrayOpPrefix + arrayOpUifSuffix + elementSort;
            ttVisitor.createTypePredUif( elementSort, funcName, 2 );
            return new UninterpretedFuncTerm( funcName , convArgs, uiSig );
        }
        
        // The boolean array case:
        if ( elementSort == booleanSort ) {
            logger.info( "Found boolean array, creating uninterpreted predicate" );
            uiSig = Signature.intSignature( 2 , false );         
            return new UninterpretedPredFormula( arrayOpPrefix + arrayOpUipSuffix, convArgs, uiSig );
        }
        
        
        // The given array is of an untranslatable sort!
        logger.info( "Found unsupported array operator, exiting with exception!" );
        throw new UnsupportedOperationException( unsupportedArrayOp + op.name() +
                                                 " Sort: " + elementSort );
    }
}
