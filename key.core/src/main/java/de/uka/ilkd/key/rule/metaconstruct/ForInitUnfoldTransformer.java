/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.statement.LoopInit;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;

/**
 * Pulls the initializor out of a for-loop. Only receives the init as a parameter, not the whole
 * for-loop.
 *
 * Example:
 *
 * \pi for (init; guard; upd) body \omega
 *
 * to:
 *
 * \pi { init' for(; guard; upd) body } \omega
 *
 * @author Benedikt Dreher
 */
public class ForInitUnfoldTransformer extends ProgramTransformer {
    /**
     * @param loopInit A loop initializer if called for a concrete program.
     */
    public ForInitUnfoldTransformer(LoopInit loopInit) {
        super("forInitUnfoldTransformer", loopInit);
    }

    /**
     * @param programSV A {@link ProgramSV} if called while parsing a taclet.
     */
    public ForInitUnfoldTransformer(ProgramSV programSV) {
        super("forInitUnfoldTransformer", programSV);
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        Debug.assertTrue(pe instanceof LoopInit, "ForInitUnfoldTransformer cannot handle ", pe);

        final LoopInit astLoopInit = (LoopInit) pe;
        final Statement[] loopInitStatementList = new Statement[astLoopInit.getInits().size()];

        for (int i = 0; i < loopInitStatementList.length; i++) {
            loopInitStatementList[i] = astLoopInit.getInits().get(i);
        }

        return loopInitStatementList;
    }
}
