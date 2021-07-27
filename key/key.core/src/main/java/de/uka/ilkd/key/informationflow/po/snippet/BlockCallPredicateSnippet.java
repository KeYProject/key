package de.uka.ilkd.key.informationflow.po.snippet;

import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.MiscTools;


/**
 * Generate term "self != null".
 * <p/>
 * @author christoph
 */
class BlockCallPredicateSnippet extends TwoStateMethodPredicateSnippet {

    @Override
    String generatePredicateName(IProgramMethod pm,
                                 StatementBlock block,
                                 LoopSpecification loopInv) {
        final String nameString =
                MiscTools.toValidTacletName("RELATED_BY_BLOCK_" + "at_line_" +
                                            block.getStartPosition().getLine() +
                                            "_in_" + pm.getUniqueName()).toString();
        return nameString;
    }
}