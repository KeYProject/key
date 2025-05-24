/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.rule.MatchConditions;

import org.key_project.logic.LogicServices;
import org.key_project.logic.PoolSyntaxElementCursor;

public final class GotoNextSiblingInstruction implements MatchInstruction {

    public static final GotoNextSiblingInstruction INSTANCE = new GotoNextSiblingInstruction();

    private GotoNextSiblingInstruction() {
    }

    @Override
    public MatchConditions match(PoolSyntaxElementCursor cursor, MatchConditions matchConditions,
            LogicServices services) {
        cursor.gotoNextSibling();
        return matchConditions;
    }
}
