/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.merge;

import java.io.File;
import java.util.Iterator;
import javax.annotation.Nonnull;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.macros.AbstractProofMacro;
import de.uka.ilkd.key.macros.FinishSymbolicExecutionUntilMergePointMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.rule.merge.procedures.MergeIfThenElseAntecedent;
import de.uka.ilkd.key.rule.merge.procedures.MergeTotalWeakening;
import de.uka.ilkd.key.util.HelperClassForTests;
import de.uka.ilkd.key.util.ProofStarter;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Test suite for the {@link MergeRule}.
 *
 * @author Dominic Scheurer
 */
public class MergeRuleTests {

    private static final File TEST_RESOURCES_DIR_PREFIX =
        new File(HelperClassForTests.TESTCASE_DIRECTORY, "merge/");

    /**
     * Simple regression test case loading an existing closed proof (standard Gcd example) including
     * two merges with ITE antecedent merges and trying to replay it.
     *
     * @throws ProblemLoaderException If the proof could not be loaded.
     */
    @Test
    public void testLoadGcdProof() {
        Proof proof = loadProof(TEST_RESOURCES_DIR_PREFIX, "gcd.closed.proof");
        assertTrue(proof.closed());
    }

    /**
     * Simple regression test case loading an existing closed proof (standard Gcd example) including
     * two merges with predicate abstraction and trying to replay it.
     *
     * @throws ProblemLoaderException If the proof could not be loaded.
     */
    @Test
    public void testLoadGcdProofWithPredAbstr() {
        Proof proof = loadProof(TEST_RESOURCES_DIR_PREFIX, "gcd.closed.predicateabstraction.proof");
        assertTrue(proof.closed());
    }

    /**
     * Simple regression test case loading an existing closed proof (standard Gcd example) including
     * two merges with predicate abstraction (with lattice elements manually chosen by the user) and
     * trying to replay it.
     *
     * @throws ProblemLoaderException If the proof could not be loaded.
     */
    @Test
    public void testLoadGcdProofWithPredAbstrAndUserChoices() {
        Proof proof = loadProof(TEST_RESOURCES_DIR_PREFIX,
            "gcd.closed.predicateAbstractionWithUserChoices.proof");
        assertTrue(proof.closed());
    }

    /**
     * Automatic proof of the Gcd problem with two merges triggered by merge point statements.
     */
    @Test
    public void testDoAutomaticGcdProofWithMergePointStatements() {
        final Proof proof = loadProof(TEST_RESOURCES_DIR_PREFIX, "gcd.mergePointStatements.key");
        startAutomaticStrategy(proof);

        assertTrue(proof.closed());

        Iterator<Node> it = proof.root().subtreeIterator();
        int mergeAppsCnt = 0;
        while (it.hasNext()) {
            if (it.next().getAppliedRuleApp() instanceof MergeRuleBuiltInRuleApp) {
                mergeAppsCnt++;
            }
        }

        Assertions.assertEquals(2, mergeAppsCnt, "There should be two merge apps.");
    }

    /**
     * Replays a closed proof of the Gcd problem with two merges triggered by merge point
     * statements.
     */
    @Test
    public void testLoadClosedGcdProofWithMergePointStatements() {
        final Proof proof =
            loadProof(TEST_RESOURCES_DIR_PREFIX, "gcd.mergePointStatements.closed.proof");

        assertTrue(proof.closed());

        Iterator<Node> it = proof.root().subtreeIterator();
        int mergeAppsCnt = 0;
        while (it.hasNext()) {
            if (it.next().getAppliedRuleApp() instanceof MergeRuleBuiltInRuleApp) {
                mergeAppsCnt++;
            }
        }

        Assertions.assertEquals(2, mergeAppsCnt, "There should be two merge apps.");
    }

    /**
     * Automatic proof of the Gcd problem with two merges triggered by merge point statements.
     */
    @Test
    public void testDoAutomaticGcdProofWithMergePointStatementAndBlockContract() {
        final Proof proof = loadProof(TEST_RESOURCES_DIR_PREFIX, "gcd.MPSAndBlockContract.key");
        startAutomaticStrategy(proof);

        assertTrue(proof.closed());

        Iterator<Node> it = proof.root().subtreeIterator();
        int mergeAppsCnt = 0;
        while (it.hasNext()) {
            if (it.next().getAppliedRuleApp() instanceof MergeRuleBuiltInRuleApp) {
                mergeAppsCnt++;
            }
        }

        Assertions.assertEquals(1, mergeAppsCnt, "There should be one merge app.");
    }

    /**
     * Regression test for a case where a merge with MPS is done after two branches with a variable
     * "result_0", which is not the same (one time an integer and one time an Object). This clash
     * has to result in a renaming. An interactive cut in the proof should make sure that the
     * renaming works and resolves the clashes. The test case includes a "is weakening" goal.
     * Underlying Java file: "A.java".
     */
    @Test
    public void testLoadProofWithDiffVarsWithSameNameAndMPS() {
        Proof proof = loadProof(TEST_RESOURCES_DIR_PREFIX,
            "A.differentVarsWithSameName.MPS.cut.closed.proof");
        assertTrue(proof.closed());
    }

    /**
     * This test case semi-automatically proves the Gcd problem with two merges in the following
     * way:
     * <p>
     *
     * <ol>
     * <li>Run the {@link FinishSymbolicExecutionUntilMergePointMacro} on the root</li>
     * <li>Do one merge</li>
     * <li>Again run the macro on the one open goal</li>
     * <li>Do another merge</li>
     * <li>Let the automatic strategy finish the proof</li>
     * </ol>
     * <p>
     * <p>
     * At the end, the proof should be closed.
     *
     * @throws ProblemLoaderException If the proof could not be loaded.
     */
    @Test
    public void testDoManualGcdProof() throws Exception {
        final Proof proof = loadProof(TEST_RESOURCES_DIR_PREFIX, "gcd.key");

        for (int i = 0; i < 2; i++) {
            runMacro(new FinishSymbolicExecutionUntilMergePointMacro(),
                proof.openGoals().head().node());
            mergeFirstGoal(proof, MergeIfThenElseAntecedent.instance());
        }

        startAutomaticStrategy(proof);
        assertTrue(proof.closed());
    }

    /**
     * Merges for SE states with different symbolic states are only allowed if the path conditions
     * are distinguishable -- for the case that if-then-else conditions are employed. This test case
     * tries to merge two states with equal path condition but different symbolic states --
     * therefore, the merge should fail due to an incomplete rule application.
     */
    @Test
    public void testMergeIndistinguishablePathConditionsWithITE() {
        final Proof proof =
            loadProof(TEST_RESOURCES_DIR_PREFIX, "IndistinguishablePathConditions.proof");

        try {
            mergeFirstGoal(proof, MergeIfThenElseAntecedent.instance());
            Assertions.fail("The merge operation should not be applicable.");
        } catch (IncompleteRuleAppException e) {
        }
    }

    /**
     * Same as testMergeIndistinguishablePathConditionsWithITE(), but with two merge partners.
     */
    @Test
    public void testMergeThreeIndistinguishablePathConditionsWithITE() {
        final Proof proof =
            loadProof(TEST_RESOURCES_DIR_PREFIX, "IndistinguishablePathConditions.twoJoins.proof");

        try {
            mergeFirstGoal(proof, MergeIfThenElseAntecedent.instance());
            Assertions.fail("The merge operation should not be applicable.");
        } catch (IncompleteRuleAppException e) {
        }
    }

    /**
     * Merges two SE states with different symbolic states and equal path condition, but uses the
     * "Full Anonymization" merge method for which this is irrelevant. The merge should succeed and
     * the proof should be closable.
     */
    @Test
    public void testMergeIndistinguishablePathConditionsWithFullAnonymization() {
        final Proof proof =
            loadProof(TEST_RESOURCES_DIR_PREFIX, "IndistinguishablePathConditions.proof");

        mergeFirstGoal(proof, MergeTotalWeakening.instance());
        startAutomaticStrategy(proof);

        assertTrue(proof.closed());
        Assertions.assertEquals(1, proof.getStatistics().mergeRuleApps);
    }

    /**
     * Runs the automatic JavaDL strategy on the given proof.
     *
     * @param proof Proof to prove automatically.
     */
    public static void startAutomaticStrategy(final Proof proof) {
        ProofStarter starter = new ProofStarter(false);
        starter.init(proof);
        starter.start();
    }

    /**
     * Merges the first open goal in the given proof. Asserts that the constructed merge rule
     * application is complete.
     *
     * @param proof The proof the first goal of which to merge with suitable partner(s).
     */
    private void mergeFirstGoal(final Proof proof, MergeProcedure mergeProc) {
        final Services services = proof.getServices();
        final MergeRule mergeRule = MergeRule.INSTANCE;

        final Goal mergeGoal = proof.openGoals().head();
        final Node mergeNode = mergeGoal.node();
        final PosInOccurrence mergePio = getPioFirstFormula(mergeNode.sequent());
        final MergeRuleBuiltInRuleApp mergeApp =
            (MergeRuleBuiltInRuleApp) mergeRule.createApp(mergePio, services);

        {
            mergeApp.setMergePartners(
                MergeRule.findPotentialMergePartners(proof.openGoals().head(), mergePio));
            mergeApp.setConcreteRule(mergeProc);
            mergeApp.setMergeNode(mergeNode);
        }

        if (!mergeApp.complete()) {
            throw new IncompleteRuleAppException();
        }

        mergeGoal.apply(mergeApp);
    }

    /**
     * @param sequent Sequent to get the PIO of the first succedent formula for.
     * @return The PIO for the first succedent formula of the given sequent.
     */
    private PosInOccurrence getPioFirstFormula(Sequent sequent) {
        return new PosInOccurrence(sequent.succedent().getFirst(), PosInTerm.getTopLevel(), false);
    }

    /**
     * Runs the given macro on the given proof node.
     *
     * @param macro The macro to execute.
     * @param node The node to execute the macro on.
     */
    private void runMacro(AbstractProofMacro macro, Node node) {
        try {
            macro.applyTo(null, node, null, null);
        } catch (Exception e) {
            Assertions.fail("Could not apply macro.");
        }
    }

    public static Proof loadProof(String directory, String proofFileName) {
        return loadProof(new File(directory), proofFileName);
    }

    /**
     * Loads the given proof file. Checks if the proof file exists and the proof is not null, and
     * fails if the proof could not be loaded.
     *
     * @param directory
     * @param proofFileName The file name of the proof file to load.
     * @return The loaded proof.
     */
    @Nonnull
    public static Proof loadProof(File directory, String proofFileName) {
        File proofFile = new File(directory, proofFileName);
        assertTrue(proofFile.exists(),
            "Proof file: " + proofFile.getAbsolutePath() + " could not be found!");

        try {
            KeYEnvironment<?> environment = KeYEnvironment.load(JavaProfile.getDefaultInstance(),
                proofFile, null, null, null, true);
            Proof proof = environment.getLoadedProof();
            Assertions.assertNotNull(proof);

            return proof;
        } catch (ProblemLoaderException e) {
            Assertions.fail("Proof could not be loaded", e);
            return null;
        }
    }

    private static class IncompleteRuleAppException extends RuntimeException {
    }
}
