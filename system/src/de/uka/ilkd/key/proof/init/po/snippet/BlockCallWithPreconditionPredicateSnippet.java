/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.util.MiscTools;


/**
 * Generate term "self != null".
 * <p/>
 * @author christoph
 */
class BlockCallWithPreconditionPredicateSnippet
        extends TwoStateMethodPredicateSnippet {

    @Override
    String generatePredicateName(IProgramMethod pm,
                                 StatementBlock block) {
        String nameSting =
                MiscTools.toValidTacletName("EXECUTION_OF_BLOCK_" + block.toString() +
                                            "_WITH_PRE").toString();
        return nameSting;
    }
}
