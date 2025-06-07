/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.vm.instruction;

import org.key_project.logic.LogicServices;
import org.key_project.logic.PoolSyntaxElementCursor;
import org.key_project.prover.rules.instantiation.MatchResultInfo;

public final class GotoNextSiblingInstruction implements VMInstruction {

    public static final GotoNextSiblingInstruction INSTANCE = new GotoNextSiblingInstruction();

    private GotoNextSiblingInstruction() {
    }

    @Override
    public MatchResultInfo match(PoolSyntaxElementCursor cursor,
            MatchResultInfo matchConditions,
            LogicServices services) {
        cursor.gotoNextSibling();
        return matchConditions;
    }
}
