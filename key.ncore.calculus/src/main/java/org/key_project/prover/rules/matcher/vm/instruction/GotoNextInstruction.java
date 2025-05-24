/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.vm.instruction;

import org.key_project.logic.LogicServices;
import org.key_project.logic.PoolSyntaxElementCursor;
import org.key_project.prover.rules.instantiation.MatchResultInfo;

public final class GotoNextInstruction implements VMInstruction {

    public static final GotoNextInstruction INSTANCE = new GotoNextInstruction();

    private GotoNextInstruction() {
    }

    @Override
    public MatchResultInfo match(PoolSyntaxElementCursor cursor,
            MatchResultInfo matchConditions,
            LogicServices services) {
        cursor.gotoNext();
        return matchConditions;
    }
}
