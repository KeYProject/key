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

import de.uka.ilkd.key.logic.op.IUpdateOperator;
import de.uka.ilkd.key.logic.op.Operator;

/** This class represents the translation rule for <tt>IUpdateOperator</tt>s.
 * <p>
 * They are currently not supported in the translation
 * 
 * @author akuwertz
 * @version 1.0,  01/29/2006
 */

public class TranslateIUpdateOperator implements IOperatorTranslation {

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.translation.IOperatorTranslation#isApplicable(de.uka.ilkd.key.logic.op.Operator)
     */
    public boolean isApplicable(Operator op) {
        return op instanceof IUpdateOperator;
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.translation.IOperatorTranslation#translate(de.uka.ilkd.key.logic.op.Operator, de.uka.ilkd.key.proof.decproc.translation.TermTranslationVisitor)
     */
    public Object translate(Operator op, TermTranslationVisitor ttVisitor) {
        // Because IUpdateOperators are currently not translated, this method should not be called!
        throw new UnsupportedOperationException();
    }
}
