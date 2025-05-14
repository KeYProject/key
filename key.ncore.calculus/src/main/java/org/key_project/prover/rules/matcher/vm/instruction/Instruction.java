/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.vm.instruction;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.prover.rules.instantiation.MatchConditions;

public abstract class Instruction {
    /**
     * Instruction argument to match against.
     */
    protected final SyntaxElement arg;

    protected Instruction(SyntaxElement arg) {
        this.arg = arg;
    }

    /**
     * tries to match the schema variable of this instruction with the specified
     * {@link SyntaxElement}
     * {@code instantiationCandidate} w.r.t. the given constraints by {@link MatchConditions}
     *
     * @param instantiationCandidate the {@link SyntaxElement} to be matched
     * @param matchCond the {@link MatchConditions} with additional constraints (e.g. previous
     *        matches of this schemavariable)
     * @param services the {@link LogicServices}
     * @return {@code null} if no matches have been found or the new {@link MatchConditions} with
     *         the pair {@code (sv, instantiationCandidate)} added
     */
    public abstract MatchConditions match(SyntaxElement instantiationCandidate,
            MatchConditions matchCond,
            LogicServices services);
}
