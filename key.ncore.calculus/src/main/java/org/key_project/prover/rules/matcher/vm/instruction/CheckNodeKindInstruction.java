/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.vm.instruction;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.prover.rules.instantiation.MatchResultInfo;

public final class CheckNodeKindInstruction implements MatchInstruction {
    private final Class<?> nodeType;

    public CheckNodeKindInstruction(Class<?> nodeType) {
        this.nodeType = nodeType;
    }

    @Override
    public MatchResultInfo match(SyntaxElement actualElement, MatchResultInfo matchConditions,
            LogicServices services) {
        if (nodeType.isInstance(actualElement)) {
            return matchConditions;
        }
        return null;
    }
}
