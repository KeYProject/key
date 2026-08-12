/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.logic.sort.ParametricSortInstance;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;

import org.jspecify.annotations.Nullable;

/**
 * Matches a parametric function instance "up to generic arguments": the source operator must be an
 * instance of the same base function as the pattern's. The generic arguments themselves are
 * matched afterward by their own instructions (a generic-sort match or an identity check per
 * argument).
 */
public class SimilarParametricSortInstruction implements MatchInstruction {
    private final ParametricSortInstance psi;

    public SimilarParametricSortInstruction(ParametricSortInstance psi) {
        this.psi = psi;
    }

    @Override
    public @Nullable MatchResultInfo match(SyntaxElement actualElement,
            MatchResultInfo matchConditions, LogicServices services) {
        if (((ParametricSortInstance) actualElement).getBase() == psi.getBase()) {
            return matchConditions;
        }
        return null;
    }
}
