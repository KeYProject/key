/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.ProofStarter;

import org.key_project.logic.PosInTerm;
import org.key_project.prover.proof.rulefilter.TacletFilter;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/// Tests that the rule app indices report the taclets without a rule set whenever the user can
/// interact with the proof: after a run of the prover, after pruning, and after a scope of the
/// automatic mode. A query in interactive mode reports them in automatic mode as well. The taclets
/// hide_left and hide_right have no rule set.
public class TestRuleAppIndexMode {
    /// A problem that the prover reduces to the open goal `p ==> q`.
    private static final String PROBLEM = "\\predicates { p; q; }\n\\problem { p -> q }\n";

    @Test
    void indicesAreInteractiveAfterARun(@TempDir Path dir) throws Exception {
        final KeYEnvironment<DefaultUserInterfaceControl> env = load(dir);
        try {
            final Proof proof = env.getLoadedProof();
            run(proof);
            assertEquals(RuleAppIndexMode.INTERACTIVE, proof.getRuleAppIndexMode());
            assertTrue(reports(proof.openGoals().head(), "hide_left", true));
        } finally {
            env.dispose();
        }
    }

    @Test
    void aPrunedGoalIsInteractive(@TempDir Path dir) throws Exception {
        final KeYEnvironment<DefaultUserInterfaceControl> env = load(dir);
        try {
            final Proof proof = env.getLoadedProof();
            run(proof);
            proof.pruneProof(proof.root());
            assertTrue(reports(proof.openGoals().head(), "hide_right", false));
        } finally {
            env.dispose();
        }
    }

    @Test
    void scopesRestoreThePreviousMode(@TempDir Path dir) throws Exception {
        final KeYEnvironment<DefaultUserInterfaceControl> env = load(dir);
        try {
            final Proof proof = env.getLoadedProof();
            final Goal goal = proof.openGoals().head();
            try (var automatic = proof.setRuleAppIndexMode(RuleAppIndexMode.AUTO)) {
                try (var interactive = proof.setRuleAppIndexMode(RuleAppIndexMode.INTERACTIVE)) {
                    assertTrue(reports(goal, "hide_right", false));
                }
                assertEquals(RuleAppIndexMode.AUTO, proof.getRuleAppIndexMode());
            }
            assertTrue(reports(goal, "hide_right", false));
        } finally {
            env.dispose();
        }
    }

    @Test
    void anInteractiveQueryReportsTacletsWithoutRuleSetInAutomaticMode(@TempDir Path dir)
            throws Exception {
        final KeYEnvironment<DefaultUserInterfaceControl> env = load(dir);
        try {
            final Proof proof = env.getLoadedProof();
            final Goal goal = proof.openGoals().head();
            final PosInOccurrence pos = new PosInOccurrence(goal.sequent().succedent().getFirst(),
                PosInTerm.getTopLevel(), false);
            try (var automatic = proof.setRuleAppIndexMode(RuleAppIndexMode.AUTO)) {
                assertTrue(goal.ruleAppIndex()
                        .getTacletAppAtAndBelow(TacletFilter.TRUE, pos, proof.getServices(),
                            RuleAppIndexMode.INTERACTIVE)
                        .stream().anyMatch(app -> app.taclet().name().toString()
                                .equals("hide_right")));
            }
        } finally {
            env.dispose();
        }
    }

    private static KeYEnvironment<DefaultUserInterfaceControl> load(Path dir) throws Exception {
        final Path problem = dir.resolve("problem.key");
        Files.writeString(problem, PROBLEM);
        return KeYEnvironment.load(problem);
    }

    private static void run(Proof proof) {
        final ProofStarter starter = new ProofStarter(false);
        starter.init(proof);
        starter.start();
    }

    /// Returns whether the index of the goal reports an app of the named taclet at the first
    /// formula of the antecedent or of the succedent.
    private static boolean reports(Goal goal, String taclet, boolean inAntecedent) {
        final SequentFormula formula = inAntecedent ? goal.sequent().antecedent().getFirst()
                : goal.sequent().succedent().getFirst();
        final PosInOccurrence pos =
            new PosInOccurrence(formula, PosInTerm.getTopLevel(), inAntecedent);
        return goal.ruleAppIndex()
                .getTacletAppAt(TacletFilter.TRUE, pos, goal.proof().getServices()).stream()
                .map(TacletApp::taclet).anyMatch(t -> t.name().toString().equals(taclet));
    }
}
