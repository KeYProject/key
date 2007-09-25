//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.decproc.translation;

import org.apache.log4j.Logger;
import de.uka.ilkd.key.logic.op.Operator;

/** This class represents the translation rule for <tt>Operator</tt>s of unknown or unexpected classes.
 * <p>
 * It only throws an <tt>Exception</tt> to indicate the occurrence of this <tt>Operator</tt> 
 * 
 * @author akuwertz
 * @version 1.0,  04/03/2006
 */

public class TranslateUnknownOp implements IOperatorTranslation {

    /* Additional fields */
    
    /** A <tt>Logger</tt> for logging and debugging operator translation */
    private static final Logger logger = Logger.getLogger( TranslateUnknownOp.class.getName() );
        // Logger is created hierarchical to inherit configuration and behaviour from parent
    
    /** String constant for error message */
    private static final String unknownOp =
        "Unknown operator occurred and could not be translated! Operator is instance of class: ";
    
    
    
    /* Public method implementation*/
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.translation.IOperatorTranslation#isApplicable(de.uka.ilkd.key.logic.op.Operator)
     */
    public boolean isApplicable(Operator op) {
        return true;
    }

    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.translation.IOperatorTranslation#translate(de.uka.ilkd.key.logic.op.Operator, de.uka.ilkd.key.proof.decproc.translation.TermTranslationVisitor)
     */
    public Object translate(Operator op, TermTranslationVisitor ttVisitor) {
        logger.info( "Found unexpected or unknown operator!" );
        logger.info( "Stopping translation of current term!" );
        throw new IllegalArgumentException( unknownOp + op.getClass() );
    }
}
