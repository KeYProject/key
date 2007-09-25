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

import de.uka.ilkd.key.logic.op.DecisionProcedureSmtAufliaOp;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.sort.ObjectSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.decproc.smtlib.ConnectiveFormula;
import de.uka.ilkd.key.proof.decproc.smtlib.Formula;
import de.uka.ilkd.key.proof.decproc.smtlib.Term;
import de.uka.ilkd.key.proof.decproc.smtlib.PredicateFormula;

/** This class represents the translation rule for an <tt>Equality</tt>.
 * <p>
 * Three different types of an <tt>Equality</tt> are currently translated:<br>
 * If the target <tt>Sort</tt> of an <tt>Equality</tt> is <tt>FORMULA</tt>, it is translated
 * into an SMT-LIB <tt>ConnectiveFormula</tt> as equivalence. The same happens for an <tt>Equality</tt> 
 * having a boolean target <tt>Sort</tt>.<br>
 * If the target <tt>Sort</tt> is an integer or object <tt>Sort</tt>, it is translated into a 
 * <tt>PredicateFormula</tt> as equality
 *   
 * @author akuwertz
 * @version 1.2,  03/27/2006  (Added support for obejct sort)
 */

public class TranslateEquality implements IOperatorTranslation {

     /* Additional fields */
    
    /** A <tt>Logger</tt> for logging and debugging operator translation */
    private static final Logger logger = Logger.getLogger( TranslateEquality.class.getName() );
        // Logger is created hierarchical to inherit configuration and behaviour from parent
    
    /* String constants for error messages */
    private static final String translationFailure = 
        "Translation of Equality operator failed due to illegal arguments on visitor stack:\n";
    private static final String failureCauseNoTerm = 
        " expected an argument of class Term (SMT-LIB) and found the object:\n";
    private static final String failureCauseNoFormula = 
        " expected an argument of class Formula (SMT-LIB) and found the object:\n";
    private static final String unsupportedEquality = "Translation of Equality failed!";
    private static final String unsupportedSort = 
        "\nCause: the sort of this equality is not supported: ";
    private static final String unsupportedOperator = 
        "\nCause: this equality operator is not supported!";
    private static final String diffArgSorts =
        "\nCause: the arguments are of different sorts: ";
    
        
    /* Public method implementation*/

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.translation.IOperatorTranslation#isApplicable(de.uka.ilkd.key.logic.op.Operator)
     */
    public boolean isApplicable(Operator op) {
        return op instanceof Equality;
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.translation.IOperatorTranslation#translate(de.uka.ilkd.key.logic.op.Operator, de.uka.ilkd.key.proof.decproc.translation.TermTranslationVisitor)
     */
    public Object translate(Operator op, TermTranslationVisitor ttVisitor) {
        
        logger.debug( "Popping 2 arguments from stack" );
        Object[] args = ttVisitor.getTranslatedArguments( 2 );
        
        if ( op == Op.EQV ) {
            logger.info( "Found 'EQV' equality, starting operator translation..." );
            
            // The FORMULA case:  f1 <-> f2 will be translated into a ConnectiveFormula
            if ( args[0] instanceof Formula  &&  args[1] instanceof Formula ) {
                Formula[] convArgs = { (Formula) args[0], (Formula) args[1] };
                logger.info( "Creating 'EQV' formula" );
                return new ConnectiveFormula( DecisionProcedureSmtAufliaOp.EQV, convArgs );
            }
            String errorMsg = translationFailure + op.name() + failureCauseNoFormula +
                              ( args[0] instanceof Formula ? args[1] : args[0] );
            throw new IllegalArgumentException( errorMsg ); 
                             
        }
        
        if ( op == Op.EQUALS ) {
            logger.info( "Found 'EQUALS' equality, starting operator translation..." );
            
            // EQUALS represents the general equality, applicable on arbitrary KeY Terms
            Sort subSortFirst = ttVisitor.getCurrentTerm().sub(0).sort();
            Sort subSortSecond = ttVisitor.getCurrentTerm().sub(1).sort();
            Sort integerSort = ttVisitor.getServices().getTypeConverter().getIntegerLDT().targetSort();
            Sort booleanSort = ttVisitor.getServices().getTypeConverter().getBooleanLDT().targetSort();
            
            // First treat equality on integers
            if ( subSortFirst.extendsTrans( integerSort )  &&  subSortSecond.extendsTrans( integerSort ) ) {
                if ( args[0] instanceof Term  &&  args[1] instanceof Term ) {
                    Term[] convArgs = { (Term) args[0], (Term) args[1] };
                    logger.info( "Treating as integer equality, creating 'EQUALS' formula" );
                    return new PredicateFormula( DecisionProcedureSmtAufliaOp.EQUALS, convArgs );
                }
                String errorMsg = translationFailure + op.name() + failureCauseNoTerm +
                                  ( args[0] instanceof Term ? args[1] : args[0] );
                throw new IllegalArgumentException( errorMsg );
            }
            
            // Next treat equality on booleans: Create a new equivalence!
            if ( subSortFirst == booleanSort  &&  subSortSecond == booleanSort ) {
                if ( args[0] instanceof Formula  &&  args[1] instanceof Formula ) {
                    Formula[] convArgs = { (Formula) args[0], (Formula) args[1] };
                    logger.info( "Treating as boolean equality, creating 'EQV' formula" );
                    return new ConnectiveFormula( DecisionProcedureSmtAufliaOp.EQV, convArgs );
                }
                String errorMsg = translationFailure + op.name() + failureCauseNoFormula +
                                  ( args[0] instanceof Formula ? args[1] : args[0] );
                throw new IllegalArgumentException( errorMsg );
            }
            
            // Finally the equality on objects 
            if ( isCompatibleObject ( subSortFirst, subSortSecond ) ) {
                if ( args[0] instanceof Term  &&  args[1] instanceof Term ) {
                    Term[] convArgs = { (Term) args[0], (Term) args[1] };
                    logger.info( "Treating as object equality, creating 'EQUALS' formula" );
                    return new PredicateFormula( DecisionProcedureSmtAufliaOp.EQUALS, convArgs );
                }
                String errorMsg = translationFailure + op.name() + failureCauseNoTerm +
                                  ( args[0] instanceof Term ? args[1] : args[0] );
                throw new IllegalArgumentException( errorMsg );
            }
            
            
            logger.info( "Found unsupported equality, exiting with exception!" );
            // Arguments are of different sorts!
            if ( subSortFirst.extendsTrans( integerSort )  ||  subSortFirst == booleanSort  ||
                 subSortFirst instanceof ObjectSort ) {
                throw new UnsupportedOperationException( unsupportedEquality + diffArgSorts + 
                                                         subSortFirst + " <-> " + subSortSecond );
            }
            
            // Given equality is of an untranslatable sort!
            throw new UnsupportedOperationException( unsupportedEquality + op.name() + 
                                                     unsupportedSort + subSortFirst );
        }
        
        // Other equality operators are not supported
        logger.info( "Found unsupported equality operator, exiting with exception!" );
        throw new UnsupportedOperationException( unsupportedEquality + op.name() + 
                                                 unsupportedOperator );
    }

    
    /** Checks whether the <tt>Sort</tt>s of two objects are compatible to be used in an equality
     * @param sortFirst the sort of the first object
     * @param sortSecond the sort of the second object
     * @return true iff both <tt>Sort</tt>s are instances of <tt>ObjectSort</tt> and if one 
     *         <tt>Sort</tt> is a subsort of the other <tt>Sort</tt> 
     */
    private boolean isCompatibleObject( Sort sortFirst, Sort sortSecond ) {
        return sortFirst instanceof ObjectSort  &&  sortSecond instanceof ObjectSort;
        // TODO Further checks necessary?
    }
}
