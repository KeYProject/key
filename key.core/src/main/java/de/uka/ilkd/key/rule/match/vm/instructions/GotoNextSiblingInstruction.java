/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.rule.MatchConditions;

import org.key_project.logic.LogicServices;
import org.key_project.logic.PoolSyntaxElementCursor;

public final class GotoNextSiblingInstruction implements MatchInstruction {
    private final int skipSibling;

    public GotoNextSiblingInstruction() {
        this(1);
    }

    public GotoNextSiblingInstruction(int size) {
        assert size > 0;
        this.skipSibling = size;
    }

    @Override
    public MatchConditions match(PoolSyntaxElementCursor cursor, MatchConditions matchConditions,
            LogicServices services) {
        cursor.gotoNextSibling(skipSibling);
        return matchConditions;
    }
}
