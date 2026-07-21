/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.mtprobe.agent;

import java.util.List;

import de.uka.ilkd.key.mtprobe.ProbeSink;

import net.bytebuddy.asm.Advice;

/**
 * Inlined into {@code BackTrackingManager.assertValidTicket}. That method is the prover's own
 * determinism guard: while it re-evaluates a feature term (to enumerate instantiations) it checks
 * that the same choice point sits at each position every time. If a different one appears, the
 * feature evaluation was not deterministic -- exactly what a shared mutable field on a feature
 * causes under the multi-core prover. We report it as an invariant violation; unlike the original
 * {@code assert}, this needs no {@code -ea} and does not abort the run.
 */
public final class ChoicePointAdvice {

    private ChoicePointAdvice() {
    }

    @Advice.OnMethodEnter
    static void onEnter(@Advice.FieldValue("position") int position,
            @Advice.FieldValue("tickets") List<Object> tickets,
            @Advice.Argument(0) Object ticket) {
        if (position < tickets.size()) {
            final Object expected = tickets.get(position);
            if (expected != ticket) {
                ProbeSink.invariantViolated("choice-point",
                    "at position " + position + " the feature evaluation reached "
                        + ticket.getClass().getName() + " where a previous evaluation had "
                        + expected.getClass().getName()
                        + " -- non-deterministic feature evaluation");
            }
        }
    }
}
