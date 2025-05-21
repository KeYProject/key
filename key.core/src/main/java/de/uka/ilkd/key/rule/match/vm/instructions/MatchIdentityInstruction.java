/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.rule.MatchConditions;

import org.key_project.logic.LogicServices;
import org.key_project.logic.PoolSyntaxElementCursor;
import org.key_project.logic.SyntaxElement;

public final class MatchIdentityInstruction
        implements de.uka.ilkd.key.rule.match.vm.instructions.MatchInstruction {

    private final SyntaxElement syntaxElement;

    public MatchIdentityInstruction(SyntaxElement syntaxElement) {
        this.syntaxElement = syntaxElement;
    }

    @Override
    public MatchConditions match(PoolSyntaxElementCursor cursor, MatchConditions matchConditions,
            LogicServices services) {
        if (syntaxElement == cursor.getCurrentElement()) {
            return matchConditions;
        }
        return null;
    }
}
