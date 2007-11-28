// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.decproc.translation;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.decproc.DecisionProcedureSmtAufliaOp;
import de.uka.ilkd.key.proof.decproc.smtlib.ConnectiveFormula;
import de.uka.ilkd.key.proof.decproc.smtlib.Formula;
import de.uka.ilkd.key.proof.decproc.smtlib.IteTerm;
import de.uka.ilkd.key.proof.decproc.smtlib.Term;


/** This class represents the translation rule for the general <tt>IfThenElse</tt> operator.
 * <p>
 * An <tt>IfThenElse</tt> operator is translated into an SMT-LIB <tt>ConnectiveFormula</tt>,
 * if it represents a choice between two <tt>Term</tt>s of <tt>Sort</tt> <tt>FORMULA</tt>. If it
 * represents a choice between two <tt>Term</tt>s of integer <tt>Sort</tt>, it is translated into
 * an SMT-LIB <tt>IteTerm</tt>.  
 *     
 * @author akuwertz
 * @version 1.1,  02/16/2006  (Added logger support)
 */

public class TranslateIfThenElse implements IOperatorTranslation {

     /* Additional fields */
    
    /** A <tt>Logger</tt> for logging and debugging operator translation */
    private static final Logger logger = Logger.getLogger( TranslateIfThenElse.class.getName() );
        // Logger is created hierarchical to inherit configuration and behaviour from parent
    
    /* String constants for error messages */
    private static final String translationFailure = 
        "Translation of IfThenElse operator failed due to illegal arguments on visitor stack!";
    private static final String failureCauseNoTerm = 
        " Expected an argument of class Term (SMT-LIB) and found the object:\n";
    private static final String failureCauseNoFormula = 
        " Expected an argument of class Formula (SMT-LIB) and found the object:\n";
    
        
    /* Public method implementation*/
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.translation.IOperatorTranslation#isApplicable(de.uka.ilkd.key.logic.op.Operator)
     */
    public boolean isApplicable( Operator op ) {
        return op instanceof IfThenElse;
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.translation.IOperatorTranslation#translate(de.uka.ilkd.key.logic.op.Operator, de.uka.ilkd.key.proof.decproc.translation.TermTranslationVisitor)
     */
    public Object translate( Operator op, TermTranslationVisitor ttVisitor ) {
        logger.debug( "Popping 3 arguments from stack" );
        Object[] args = ttVisitor.getTranslatedArguments( 3 );
        if ( args[0] instanceof Formula ) { 
            Formula condFormula = (Formula) args[0]; 
            String errorMsg = translationFailure;
            // Further translation depends on the class of the already translated arguments 
            if ( args[1] instanceof Formula  &&  args[2] instanceof Formula ) {
                logger.info( "Found ifThenElse operator on formulae, creating 'ifthenelse' " +
                             "formula" );
                Formula[] convArgs = { condFormula, (Formula) args[1], (Formula) args[2] };    
                return new ConnectiveFormula( DecisionProcedureSmtAufliaOp.IFTHENELSE, convArgs );
            }
            if ( args[1] instanceof Term  &&  args[2] instanceof Term ) {
                logger.info( "Found ifThenElse operator on terms, creating IteTerm" );
                return new IteTerm( (Term) args[1], (Term) args[2], condFormula );
            }
            
            // Throw an appropriate error message:
            // If one argument is of class Formula, throw an formula error
            if ( args[1] instanceof Formula  ||  args[2] instanceof Formula ) {
                errorMsg += failureCauseNoFormula + (args[1] instanceof Formula ? args[2] : args[1]);
                throw new IllegalArgumentException( errorMsg );
            }
            // Else throw a Term error
            errorMsg += failureCauseNoTerm + ( args[1] instanceof Term ? args[2] : args[1] );
            throw new IllegalArgumentException( errorMsg );
        }
        
        // First argument was not of class Formula
        logger.info( "Found unsupported ifThenElse operator, exiting with exception!" );
        throw new UnsupportedOperationException( translationFailure + failureCauseNoFormula + args[0] );
    }
}
