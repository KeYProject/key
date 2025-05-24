/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.vm.instruction;

import org.key_project.logic.LogicServices;
import org.key_project.logic.PoolSyntaxElementCursor;
import org.key_project.logic.SyntaxElement;
import org.key_project.prover.rules.instantiation.MatchResultInfo;

/**
 * Convenience interface for vm instructions that do not manipulate
 * the {@link PoolSyntaxElementCursor},
 * but perform matching operations on the {@link SyntaxElement}
 * at which the cursor is positioned.
 */
public interface MatchInstruction extends VMInstruction {

    @Override
    default MatchResultInfo match(PoolSyntaxElementCursor cursor,
            MatchResultInfo matchResultInfo,
            LogicServices services) {
        return match(cursor.getCurrentElement(), matchResultInfo, services);
    }

    MatchResultInfo match(SyntaxElement actualElement,
            MatchResultInfo matchConditions, LogicServices services);
}
