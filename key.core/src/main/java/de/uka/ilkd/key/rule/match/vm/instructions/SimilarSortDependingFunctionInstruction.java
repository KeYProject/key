/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.rule.MatchConditions;

import org.key_project.logic.LogicServices;
import org.key_project.logic.PoolSyntaxElementCursor;
import org.key_project.logic.SyntaxElement;

public final class SimilarSortDependingFunctionInstruction implements MatchInstruction {
    private final SortDependingFunction sortDependingFunction;

    public SimilarSortDependingFunctionInstruction(SortDependingFunction sortDependingFunction) {
        this.sortDependingFunction = sortDependingFunction;
    }

    @Override
    public MatchConditions match(PoolSyntaxElementCursor cursor, MatchConditions matchConditions,
            LogicServices services) {
        final SyntaxElement syntaxElement = cursor.getCurrentElement();
        if (((SortDependingFunction) syntaxElement).isSimilar(sortDependingFunction)) {
            return matchConditions;
        }
        return null;
    }
}
