/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.util.MiscTools;


/**
 * Generate term "self != null".
 * <p/>
 * @author christoph
 */
class MethodCallPredicateSnippet extends TwoStateMethodPredicateSnippet {

    @Override
    String generatePredicateName(IProgramMethod pm) {
        String nameString =
                MiscTools.toValidTacletName("RELATED_BY_" + pm.getFullName()).toString();
        return nameString;
    }
}
