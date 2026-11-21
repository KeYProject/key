/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.prove;

import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTRule;
import de.uka.ilkd.key.smt.SMTSolverResult;
import de.uka.ilkd.key.smt.SMTTestSettings;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.smt.solvertypes.SolverTypeImplementation;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;
import de.uka.ilkd.key.speclang.Contract;

import org.key_project.key.cli.Log;
import org.key_project.key.cli.Verbosity;

import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * Tests {@link SmtCounters} on real proofs and pins the §2 semantics of the result record:
 * {@code smtCalls} is KeY's {@code smtSolverApps} proof statistic, i.e. the number of committed
 * SMT rule applications; an SMT rule application is committed only when the SMT solver proved
 * the goal's sequent, so {@code smtCalls} is the number of sequents closed by SMT — not the total
 * number of SMT solver invocations. {@code smtProved} is the number of closed goals whose node
 * carries an SMT rule application, which equals {@code smtCalls} in a finished proof.
 * <p>
 * The first test needs no solver: an SMT rule application records a committed solver proof, so it
 * can be applied directly. The remaining tests run the real Z3 solver on the pure first-order
 * {@code fixtures/smt} problems and are skipped when Z3 is not installed; like the SMT tests of
 * key.core, they fail instead of skipping when the environment variable
 * {@code failIfSmtSolverIsUnavailable} or {@code GITHUB_ACTIONS} is set.
 */
@Tag("slow")
class SmtCountersProofTest {

    private static final String ONE_NAME =
        "C[C::one()].JML normal_behavior operation contract.0";

    @BeforeAll
    static void quietLogs() {
        Log.configureLogging(Verbosity.ERROR);
    }

    /**
     * A committed SMT rule application counts as one call and one proved goal and matches KeY's
     * {@code smtSolverApps} proof statistic; no solver is invoked in this test.
     */
    @Test
    @Timeout(300)
    void committedSmtRuleAppIsCountedFromTheProofStatistics() throws Exception {
        try (KeYEnvironment<?> environment = KeYEnvironment.load(Fixtures.indexKey())) {
            Proof proof = createProof(environment, ONE_NAME);
            try {
                Goal goal = proof.openGoals().head();
                applySmtRuleApp(goal, "z3");
                assertThat(proof.openGoals()).isEmpty();

                SmtCounters.Counts counts = SmtCounters.of(proof);

                assertThat(counts.smtCalls()).isEqualTo(1);
                assertThat(counts.smtProved()).isEqualTo(1);
                assertThat(counts.smtCalls()).isEqualTo(proof.getStatistics().smtSolverApps);
            } finally {
                proof.dispose();
            }
        }
    }

    /**
     * An SMT solver invocation that proves the sequent is committed as a rule application: both
     * counters are 1 and {@code smtCalls} matches KeY's {@code smtSolverApps} proof statistic.
     */
    @Test
    @Timeout(300)
    void solverProvedSequentIsCountedFromTheProofStatistics() throws Exception {
        SolverType z3 = assumeZ3Installed();
        try (KeYEnvironment<?> environment = KeYEnvironment.load(Fixtures.smtValidKey())) {
            Proof proof = Objects.requireNonNull(environment.getLoadedProof());
            Goal goal = proof.openGoals().head();
            SMTProblem problem = runZ3(z3, proof, goal);
            assertThat(problem.getFinalResult().isValid())
                    .as("Z3 verdict on the valid goal x = x")
                    .isEqualTo(SMTSolverResult.ThreeValuedTruth.VALID);

            applySmtRuleApp(goal, z3.getName());
            assertThat(proof.openGoals()).isEmpty();

            SmtCounters.Counts counts = SmtCounters.of(proof);

            assertThat(counts.smtCalls()).isEqualTo(1);
            assertThat(counts.smtProved()).isEqualTo(1);
            assertThat(counts.smtCalls()).isEqualTo(proof.getStatistics().smtSolverApps);
        }
    }

    /**
     * An SMT solver invocation that does not close the goal is not committed as a rule
     * application: both counters stay 0, so {@code smtCalls} is not the total number of solver
     * invocations. The fixture states {@code x = 0} for an integer constant {@code x}, which is
     * not valid, so the solver cannot prove the goal — depending on the solver version it reports
     * a counterexample or gives up with {@code UNKNOWN}.
     */
    @Test
    @Timeout(300)
    void solverInvokedWithoutClosingLeavesTheCountersZero() throws Exception {
        SolverType z3 = assumeZ3Installed();
        try (KeYEnvironment<?> environment = KeYEnvironment.load(Fixtures.smtInvalidKey())) {
            Proof proof = Objects.requireNonNull(environment.getLoadedProof());
            Goal goal = proof.openGoals().head();
            SMTProblem problem = runZ3(z3, proof, goal);

            assertThat(problem.getFinalResult().isValid())
                    .as("Z3 verdict on the non-valid goal x = 0")
                    .isNotEqualTo(SMTSolverResult.ThreeValuedTruth.VALID);

            SmtCounters.Counts counts = SmtCounters.of(proof);

            assertThat(counts.smtCalls()).isZero();
            assertThat(counts.smtProved()).isZero();
            assertThat(proof.getStatistics().smtSolverApps).isZero();
            assertThat(proof.openGoals()).hasSize(1);
        }
    }

    /**
     * Creates the proof of the contract with the given canonical name in the given environment.
     *
     * @param environment the loaded environment
     * @param contractName the canonical contract name
     * @return the created proof with its single open root goal
     */
    private static Proof createProof(KeYEnvironment<?> environment, String contractName) {
        ContractIndex index = ContractIndex.fromEnvironment(environment);
        List<Contract> selected = index.byNames(contractName);
        assertThat(selected).as("contract " + contractName).hasSize(1);
        return HeadlessProver.createProof(environment, selected.get(0));
    }

    /**
     * Runs the Z3 solver on the given goal, like key.core's {@code smt} proof-script command does.
     *
     * @param z3 the Z3 solver type
     * @param proof the proof of the goal
     * @param goal the open goal to run the solver on
     * @return the SMT problem with the solver's final result
     */
    private static SMTProblem runZ3(SolverType z3, Proof proof, Goal goal) {
        SMTProblem problem = new SMTProblem(goal);
        new SolverLauncher(new SMTTestSettings()).launch(problem, proof.getServices(), z3);
        return problem;
    }

    /**
     * Commits the SMT rule application on the given goal, like key.core's {@code smt} proof-script
     * command does once the solver proved the sequent.
     *
     * @param goal the open goal to close
     * @param solverName the name of the solver that proved the sequent
     */
    private static void applySmtRuleApp(Goal goal, String solverName) {
        IBuiltInRuleApp app = SMTRule.INSTANCE.createApp(solverName);
        app = app.tryToInstantiate(goal);
        goal.apply(app);
    }

    /**
     * Returns the Z3 solver type, or aborts (skips) the test when Z3 is not installed; when the
     * environment variable {@code failIfSmtSolverIsUnavailable} or {@code GITHUB_ACTIONS} is
     * set, a missing Z3 fails the test instead (the house pattern of key.core's SMT tests).
     *
     * @return the installed Z3 solver type
     */
    private static SolverType assumeZ3Installed() {
        SolverType z3 = SolverTypes.getSolverTypes().stream()
                .filter(it -> it.getClass().equals(SolverTypeImplementation.class)
                        && it.getName().equals("Z3"))
                .findFirst().orElse(null);
        if (z3 != null && z3.isInstalled(true)) {
            return z3;
        }
        boolean failIfUnavailable =
            Boolean.parseBoolean(System.getenv("failIfSmtSolverIsUnavailable"))
                    || Boolean.parseBoolean(System.getenv("GITHUB_ACTIONS"));
        if (failIfUnavailable) {
            fail("required SMT solver not installed");
        }
        Assumptions.abort("required SMT solver not installed");
        throw new AssertionError("unreachable");
    }
}
