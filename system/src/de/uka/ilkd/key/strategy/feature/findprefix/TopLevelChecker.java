/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.strategy.feature.findprefix;

import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.Operator;


/**
 *
 * @author christoph
 */
class TopLevelChecker implements Checker {
    private boolean topLevel;

    @Override
    public void initPrefixCheck(PosInOccurrence p_pos) {
        topLevel = p_pos.isTopLevel();
    }


    @Override
    public void checkOperator(Operator op,
                              PIOPathIterator it) {
        // do nothing
    }


    @Override
    public boolean getResult() {
        return topLevel;
    }

}
