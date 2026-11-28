/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.prove;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.smt.SMTRule;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.Rule;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.RuleExecutor;
import org.key_project.prover.sequent.PosInOccurrence;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Unit tests for the SMT counter helper: {@code smtProved} counts the closed goals whose closing
 * rule application is an SMT rule app, and {@code smtCalls} is taken over from KeY's
 * {@code smtSolverApps} proof statistic, i.e. it counts the sequents closed by an SMT rule
 * application rather than all solver invocations.
 */
class SmtCountersTest {

    @Test
    void countsOnlySmtClosingRuleApps() {
        RuleApp smt1 = SMTRule.INSTANCE.createApp("z3");
        RuleApp smt2 = SMTRule.INSTANCE.createApp("cvc5");
        RuleApp close1 = fakeRuleApp("CloseRule");
        RuleApp close2 = fakeRuleApp("AssertRule");

        List<@Nullable RuleApp> closingApps = new ArrayList<>();
        closingApps.add(smt1);
        closingApps.add(close1);
        closingApps.add(null);
        closingApps.add(smt2);
        closingApps.add(close2);

        SmtCounters.Counts counts = SmtCounters.count(3, closingApps);

        assertThat(counts.smtCalls()).isEqualTo(3);
        assertThat(counts.smtProved()).isEqualTo(2);
    }

    @Test
    void withoutClosedGoalsBothCountersAreZero() {
        SmtCounters.Counts counts = SmtCounters.count(0, List.of());

        assertThat(counts.smtCalls()).isZero();
        assertThat(counts.smtProved()).isZero();
    }

    @Test
    void withClosedGoalsButNoSmtOnlyCallsAreCounted() {
        List<@Nullable RuleApp> closingApps = new ArrayList<>();
        closingApps.add(fakeRuleApp("CloseRule"));
        closingApps.add(null);
        SmtCounters.Counts counts = SmtCounters.count(5, closingApps);

        assertThat(counts.smtCalls()).isEqualTo(5);
        assertThat(counts.smtProved()).isZero();
    }

    /**
     * Creates a rule application that is not an SMT rule app, so the counter must not count it.
     *
     * @param name the name of the (fake) rule
     * @return a non-SMT rule application
     */
    private static RuleApp fakeRuleApp(String name) {
        Rule rule = new Rule() {
            @Override
            public Name name() {
                return new Name(name);
            }

            @Override
            public <G extends ProofGoal<G>> RuleExecutor<G> getExecutor() {
                throw new UnsupportedOperationException("test stub");
            }
        };
        return new RuleApp() {
            @Override
            public Rule rule() {
                return rule;
            }

            @Override
            public void checkApplicability() {
            }

            @Override
            public void registerSkolemConstants(Namespace<@NonNull Function> fns) {
            }

            @Override
            public boolean complete() {
                return true;
            }

            @Nullable
            @Override
            public PosInOccurrence posInOccurrence() {
                return null;
            }
        };
    }
}
