/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.logic.op.ParametricFunctionInstance;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;

import org.jspecify.annotations.Nullable;

public class SimilarParametricFunctionInstruction implements MatchInstruction {
    private final ParametricFunctionInstance pfi;

    public SimilarParametricFunctionInstruction(ParametricFunctionInstance pfi) {
        this.pfi = pfi;
    }

    @Override
    public @Nullable MatchResultInfo match(SyntaxElement actualElement,
            MatchResultInfo matchConditions, LogicServices services) {
        if (((ParametricFunctionInstance) actualElement).getBase() == pfi.getBase()) {
            return matchConditions;
        }
        return null;
    }
}
