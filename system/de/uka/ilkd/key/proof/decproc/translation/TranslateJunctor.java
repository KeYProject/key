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

import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.proof.decproc.DecisionProcedureSmtAufliaOp;
import de.uka.ilkd.key.proof.decproc.smtlib.ConnectiveFormula;
import de.uka.ilkd.key.proof.decproc.smtlib.Formula;
import de.uka.ilkd.key.proof.decproc.smtlib.TruthValueFormula;

/** This class represents the translation rule for <tt>Junctor</tt>s.
 * <p>
 * The following <tt>Junctor</tt> instances are translated currently:<ul>
 * <li>NOT</li>     <li>AND</li>
 * <li>OR</li>      <li>IMP</li>
 * <li>TRUE</li>    <li>FALSE</li></ul>
 * <p>
 * Each of the first four <tt>Junctor</tt>s mentioned above is translated into a corresponding
 * SMT-LIB <tt>ConnectiveFormula</tt>. The last two are translated into a corresponding
 * <tt>TruthValueFormula</tt>
 *  
 * @author akuwertz
 * @version 1.1,  02/15/2006  (Added logger support)
 */

public class TranslateJunctor implements IOperatorTranslation {

    /* Additional fields */
    
    /** A <tt>Logger</tt> for logging and debugging operator translation */
    private static final Logger logger = Logger.getLogger( TranslateJunctor.class.getName() );
        // Logger is created hierarchical to inherit configuration and behaviour from parent
    
    /* String constants for error messages */
    private static final String translationFailure = 
        "Translation of junctor failed due to illegal arguments on visitor stack:\n";
    private static final String failureCauseNoFormula = 
        " expected an argument of class (SMT-LIB) Formula and found the object:\n";
    private static final String unsupportedJunctor = 
        "Translation of junctor failed because this junctor is not supported by this class: ";
    
        
    /* Public method implementation*/
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.translation.IOperatorTranslation#isApplicable(de.uka.ilkd.key.logic.op.Operator)
     */
    public boolean isApplicable( Operator op ) {
        return op instanceof Junctor;
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.translation.IOperatorTranslation#translate(de.uka.ilkd.key.logic.op.Operator, de.uka.ilkd.key.proof.decproc.translation.TermTranslationVisitor)
     */
    public Object translate( Operator op, TermTranslationVisitor ttVisitor ) {
        
        if ( op == Op.TRUE ) {
            logger.info( "Found 'TRUE' junctor, creating 'true' formula" );
            return TruthValueFormula.getInstance( true );
        }
        if ( op == Op.FALSE ) {
            logger.info( "Found 'FALSE' junctor, creating 'false' formula" );
            return TruthValueFormula.getInstance( false );
        }
        
        // Temporal variables for operators of positive arity
        Object[] args;
        Formula[] convArgs;
        
        if ( op == Op.NOT ) {
            logger.info( "Found 'NOT' junctor, starting operator translation..." );
            logger.debug( "Popping 1 argument formula from stack" );
            args = ttVisitor.getTranslatedArguments( 1 );
            if ( args[0] instanceof Formula ) {
                convArgs = new Formula[] { (Formula) args[0] };
                logger.info( "Creating 'NOT' formula" );
                return new ConnectiveFormula( DecisionProcedureSmtAufliaOp.NOT, convArgs );
            }
            throw new IllegalArgumentException( translationFailure + op.name() + 
                                                failureCauseNoFormula + args[0] );
        }

        // Operators of arity 2
        if ( op == Op.AND  ||  op == Op.OR  ||  op == Op.IMP ) {
            logger.debug( "Popping 2 argument formulae from stack" );
            args = ttVisitor.getTranslatedArguments( 2 );
            if ( args[0] instanceof Formula  &&  args[1] instanceof Formula ) {
                convArgs = new Formula[] { (Formula) args[0], (Formula) args[1] };
                if ( op == Op.AND ) {
                    logger.info( "Found 'AND' junctor, creating 'AND' formula" );
                    return new ConnectiveFormula( DecisionProcedureSmtAufliaOp.AND, convArgs );
                }
                if ( op == Op.OR ) {
                    logger.info( "Found 'OR' junctor, creating 'OR' formula" );
                    return new ConnectiveFormula( DecisionProcedureSmtAufliaOp.OR, convArgs );
                }
                logger.info( "Found 'IMP' junctor, creating 'IMP' formula" );
                return new ConnectiveFormula( DecisionProcedureSmtAufliaOp.IMP, convArgs );
            }
            String errorMsg = translationFailure + op.name() + failureCauseNoFormula;
            errorMsg += args[0] instanceof Formula ? args[1] : args[0];
            throw new IllegalArgumentException( errorMsg );
        }
        
        // Unsupported junctor
        logger.info( "Found unsupported junctor, exiting with exception!" );
        throw new UnsupportedOperationException( unsupportedJunctor + op.name() );
    }
}
