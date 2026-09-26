/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.logic.GenericArgument;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;

import org.jspecify.annotations.Nullable;

/**
 * Matches a GenericArgument by the identity of its sort
 */
public class MatchBySortIdentityInstruction implements MatchInstruction {
    private final Sort patternSort;

    public MatchBySortIdentityInstruction(Sort patternSort) {
        this.patternSort = patternSort;
    }

    @Override
    public @Nullable MatchResultInfo match(SyntaxElement actualElement,
            MatchResultInfo matchConditions, LogicServices services) {
        return actualElement instanceof GenericArgument(Sort sort) && sort == patternSort
                ? matchConditions
                : null;
    }
}
