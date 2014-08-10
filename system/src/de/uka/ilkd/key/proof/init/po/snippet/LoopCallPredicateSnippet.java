/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.util.MiscTools;

public class LoopCallPredicateSnippet extends TwoStateMethodPredicateSnippet {
    @Override
    String generatePredicateName(IProgramMethod pm,
                                 StatementBlock block,
                                 LoopInvariant loopInv) {
        final String nameString =
                MiscTools.toValidTacletName("RELATED_BY_LOOP_" + "at_line_" +
                                            loopInv.getLoop().getStartPosition().getLine() +
                                            "_in_" + pm.getUniqueName()).toString();
        return nameString;
    }
}