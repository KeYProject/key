// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.decproc.translation;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.decproc.DecisionProcedureSmtAufliaOp;
import de.uka.ilkd.key.proof.decproc.smtlib.ConnectiveFormula;
import de.uka.ilkd.key.proof.decproc.smtlib.Formula;
import de.uka.ilkd.key.proof.decproc.smtlib.QuantifierFormula;
import de.uka.ilkd.key.proof.decproc.smtlib.TermVariable;

/** This class represents the translation rule for <tt>Quantifier</tt>s.<br>
 * They are supported only in AUFLIA, not in QF_AUFLIA. 
 * <p> 
 * A <tt>Quantifier</tt> is translated into a <tt>QuantifierFormula</tt>, if it is an ALL or 
 * an EXISTS quantifier. Thereby, its bound variables will also be translated
 * 
 * @author akuwertz
 * @version 1.2,  11/09/2006  (Added type predicates for quantified variables)
 */

public class TranslateQuantifier implements IOperatorTranslation {

    /* Additional fields */
           
    /** A <tt>Logger</tt> for logging and debugging operator translation */
    private static final Logger logger = Logger.getLogger( TranslateQuantifier.class.getName() );
    // Logger is created hierarchical to inherit configuration and behaviour from parent
    
    /* String constants for error messages */
    private static final String translationFailure = 
        "Translation of quantifier failed due to illegal arguments on visitor stack:\n";
    private static final String failureCauseNoFormula = 
        " expected an argument of class Formula (SMT-LIB) and found the object:\n";
    private static final String unsupportedQuantifier = "Translation of quantifier failed!";
    private static final String unsupportedOperator = 
        "\nCause: this quantifier operator is not supported!";
    private static final String unsupportedVar =
        "\nCause: the quantified variable cound not be translated: ";
    private static final String varTransFailed = 
        "\nThe following exception was thrown during variable translation: \n";
        
    
    
    /* Public methods */

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.translation.IOperatorTranslation#isApplicable(de.uka.ilkd.key.logic.op.Operator)
     */
    public boolean isApplicable( Operator op ) {
        return op instanceof Quantifier;
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.translation.IOperatorTranslation#translate(de.uka.ilkd.key.logic.op.Operator, de.uka.ilkd.key.proof.decproc.translation.TermTranslationVisitor)
     */
    public Object translate( Operator op, TermTranslationVisitor ttVisitor ) {
        
        if ( op == Op.ALL  ||  op == Op.EX ) {
            String opName = op == Op.ALL ? DecisionProcedureSmtAufliaOp.FORALL : 
                                           DecisionProcedureSmtAufliaOp.EXISTS;
            logger.info( "Found '" + opName + "' quantifier, starting operator translation..." );
            logger.debug( "Popping one argument term from stack" );
            
            Object arg = ttVisitor.getTranslatedArguments( 1 )[0];
            Formula form;
            if ( arg instanceof Formula ) form = (Formula) arg;
                else throw new IllegalArgumentException ( translationFailure + opName + 
                                                          failureCauseNoFormula + arg );
            
            ArrayOfQuantifiableVariable boundVars = ttVisitor.getCurrentTerm().varsBoundHere(0);
            logger.info( "Found "+ boundVars.size() + 
                         " quantifiable variables, trying to create new term variables..." );
            TermVariable[] quantVars = new TermVariable[ boundVars.size() ];
            Formula[] typePreds = new Formula[ boundVars.size() ];
            for ( int i = 0; i < quantVars.length; i++ ) {
                QuantifiableVariable var = boundVars.getQuantifiableVariable( i );
                // Give the quantifiable variable to the ttVisitor!
                try {
                    quantVars[i] = ttVisitor.translateLvManually( (LogicVariable) var );
                    // ClassCastExceptions will also be catched!
                } catch (RuntimeException e) {
                    // Pass on the exception after adding some quantifier specific information
                    throw new UnsupportedOperationException( unsupportedQuantifier + op.name() +
                                                             unsupportedVar + var + varTransFailed + e );
                }
                // Create type predicate for quantifiable variable
                typePreds[i] = ttVisitor.createTypePredLv( var.sort() , quantVars[i] );
            }
            logger.info( "Creating new quantifier formula!" );
            // Integrate type predicates and quantified formula
            Formula preconditions = typePreds[0];  
            Formula[] helper;
            for ( int i = 1; i < typePreds.length; i++ ) {  // typePreds.length > 0!
                helper = new Formula[]{ preconditions , typePreds[i] };
                preconditions = new ConnectiveFormula( DecisionProcedureSmtAufliaOp.AND, helper );
            }
            helper = new Formula[]{ preconditions, form };
            if ( op == Op.ALL ) {
                form = new ConnectiveFormula( DecisionProcedureSmtAufliaOp.IMP, helper );
            } else {  // op == Op.EX
                form = new ConnectiveFormula( DecisionProcedureSmtAufliaOp.AND, helper );
            }    
            return new QuantifierFormula( opName, quantVars, form ); 
        }
        
        // Other quantifier operators are not supported
        logger.info( "Found unsupported quantifier operator, exiting with exception!" );
        throw new UnsupportedOperationException( unsupportedQuantifier + ((Quantifier) op).name() +  
                                                 unsupportedOperator );
    }
    
}
