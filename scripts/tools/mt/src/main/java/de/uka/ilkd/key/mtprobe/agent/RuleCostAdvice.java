/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.mtprobe.agent;

import de.uka.ilkd.key.mtprobe.ProbeSink;

import net.bytebuddy.asm.Advice;

/**
 * Inlined into {@code RuleAppContainer.compareTo}. The prover keeps its applicable rules in a
 * priority queue ordered by this comparison. If it returns {@code 0} for two <em>different</em>
 * containers, the queue cannot tell them apart and falls back to the order they happened to be
 * inserted -- which, under the multi-core prover, depends on worker timing. So every such tie is a
 * spot where proof search could become order-dependent. We report it as an invariant violation
 * (a warning: a tie is a latent risk, not proof of an actual divergence).
 */
public final class RuleCostAdvice {

    private RuleCostAdvice() {
    }

    @Advice.OnMethodExit
    static void onExit(@Advice.This Object self, @Advice.Argument(0) Object other,
            @Advice.Return int result) {
        if (result == 0 && self != other) {
            ProbeSink.warn("rule-cost",
                "two distinct rule applications compared equal, so their order is decided by "
                    + "queue insertion (timing-dependent under the multi-core prover): "
                    + self + " vs " + other);
        }
    }
}
