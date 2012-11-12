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
class MethodCallWithPreconditionPredicateSnippet extends TwoStateMethodPredicateSnippet {

    @Override
    String generatePredicateName(IProgramMethod pm) {
        String nameSting =
                MiscTools.toValidTacletName("EXECUTION_OF_" + pm.getFullName() + "_WITH_PRE").toString();
        return nameSting;
    }
}
