/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.prove;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.smt.SMTRuleApp;

import org.key_project.prover.rules.RuleApp;

import org.jspecify.annotations.Nullable;

/**
 * Computes the SMT counters of the {@code KEY_RESULT} record (§2 of the headless interface spec)
 * from a finished proof:
 * <ul>
 * <li>{@code smtCalls} is the number of sequents the proof closed by an SMT rule application,
 * taken from the proof statistics
 * ({@link de.uka.ilkd.key.proof.Statistics#smtSolverApps}).
 * <li>{@code smtProved} counts the closed goals whose node carries an SMT rule app, i.e. the goals
 * closed by SMT.
 * </ul>
 * Because an SMT rule app is committed only when the solver proved the sequent, {@code smtCalls}
 * is <em>not</em> the total number of SMT solver invocations: a solver run that reports a
 * counterexample or gives up is not counted. Consequently both counters agree in a finished proof
 * (every closed goal carrying an SMT rule app was counted by the statistics, and vice versa).
 * Both counters are {@code 0} when SMT is not used (the default).
 * <p>
 * The counters are computed by walking the finished proof tree, because headless runs keep closed
 * goals in the tree (pruning of closed branches is disabled by default) and therefore cannot rely
 * on {@link Proof#closedGoals()}, which stays empty in that case.
 */
public final class SmtCounters {

    private SmtCounters() {
    }

    /**
     * The SMT counters of one result record.
     *
     * @param smtCalls the number of sequents closed by an SMT rule application (KeY's
     *        {@code smtSolverApps} statistic), not the total number of solver invocations
     *        ({@code 0} unless SMT is enabled)
     * @param smtProved the number of closed goals whose closing rule app is an SMT rule app,
     *        equal to {@code smtCalls} in a finished proof ({@code 0} unless SMT is enabled)
     */
    public record Counts(int smtCalls, int smtProved) {
    }

    /**
     * Computes the SMT counters of the given finished proof.
     *
     * @param proof the finished proof
     * @return the SMT counters
     */
    public static Counts of(Proof proof) {
        return count(proof.getStatistics().smtSolverApps, closingRuleAppsOfClosedGoals(proof));
    }

    /**
     * The testable core of the counting: given the number of SMT solver invocations from the
     * proof statistics and the closing rule app of every closed goal of the proof, computes the
     * SMT counters. A closed goal counts as proved via SMT iff its closing rule app is an
     * {@link SMTRuleApp}.
     *
     * @param smtCalls the number of sequents closed by an SMT rule application, as recorded by
     *        {@code Statistics.smtSolverApps}
     * @param closingRuleApps the closing rule app of each closed goal ({@code null} for a closed
     *        goal without a rule app, e.g. the root goal of a trivially closed proof)
     * @return the SMT counters
     */
    static Counts count(int smtCalls, Iterable<@Nullable RuleApp> closingRuleApps) {
        int smtProved = 0;
        for (RuleApp app : closingRuleApps) {
            if (app instanceof SMTRuleApp) {
                smtProved++;
            }
        }
        return new Counts(smtCalls, smtProved);
    }

    /**
     * Collects the closing rule app of every closed goal (closed node) of the finished proof.
     *
     * @param proof the finished proof
     * @return one entry per closed goal, in tree order
     */
    private static List<@Nullable RuleApp> closingRuleAppsOfClosedGoals(Proof proof) {
        List<@Nullable RuleApp> closingApps = new ArrayList<>();
        Iterator<Node> it = proof.root().subtreeIterator();
        while (it.hasNext()) {
            Node node = it.next();
            if (node.isClosed()) {
                closingApps.add(node.getAppliedRuleApp());
            }
        }
        return closingApps;
    }
}
