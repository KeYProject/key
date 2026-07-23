/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.merge;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.macros.AbstractProofMacro;
import de.uka.ilkd.key.macros.FinishSymbolicExecutionUntilMergePointMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.rule.merge.procedures.MergeIfThenElseAntecedent;
import de.uka.ilkd.key.rule.merge.procedures.MergeTotalWeakening;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.util.HelperClassForTests;
import de.uka.ilkd.key.util.ProofStarter;

import org.key_project.logic.Name;
import org.key_project.logic.PosInTerm;
import org.key_project.logic.op.Operator;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;

import org.jspecify.annotations.NonNull;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Test suite for the {@link MergeRule}.
 *
 * @author Dominic Scheurer
 */
public class MergeRuleTests {
    private static final Path TEST_RESOURCES_DIR_PREFIX =
        HelperClassForTests.TESTCASE_DIRECTORY.resolve("merge/");
    private static final Logger LOGGER = LoggerFactory.getLogger(MergeRuleTests.class);

    /**
     * Simple regression test case loading an existing closed proof (standard Gcd example)
     * including two merges with ITE antecedent merges and trying to replay it.
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
     *
     * Unfortunately, this test case was broken by a change in the taclet database. I replaced the
     * proof file by the automatic proof for the same proof obligation, hoping that the same issue
     * is still covered. M.U. 2/2026
     */
    @Test
    public void testLoadProofWithDiffVarsWithSameNameAndMPS() {
        Proof proof = loadProof(TEST_RESOURCES_DIR_PREFIX,
            "A.differentVarsWithSameName.MPS.cut.closed.proof");
        assertTrue(proof.closed());
    }

    /**
     * The merge rule resolves name clashes between the merge participants by minting renamed
     * symbols (see {@code MergeRuleUtils.renameMergeParticipantOp}); further fresh symbols are
     * minted by anonymisation. These symbols occur in the merged sequent, so the goal's
     * namespaces must keep resolving them: both across the rule-application commit (a goal's
     * namespaces are rebuilt from the shared base plus the node-local symbol storage) and across
     * pruning (which performs the same rebuild). This test drives the A.java clash scenario
     * (both branch contracts mint {@code result_0}/{@code exc_0}, of different sorts) LIVE,
     * without any reload: a reloaded proof would mask a loss because replay re-derives all names
     * from the saved name recorder.
     */
    @Test
    public void testMergeMintedSymbolsSurviveCommitAndPrune() {
        // closed-branch pruning must be enabled BEFORE proving: only then does closeGoal record
        // the closed goals that pruning later reopens
        final boolean oldNoPruningClosed = GeneralSettings.noPruningClosed;
        GeneralSettings.noPruningClosed = false;
        try {
            doTestMergeMintedSymbolsSurviveCommitAndPrune();
        } finally {
            GeneralSettings.noPruningClosed = oldNoPruningClosed;
        }
    }

    private void doTestMergeMintedSymbolsSurviveCommitAndPrune() {
        final Proof proof =
            loadProof(TEST_RESOURCES_DIR_PREFIX, "A.differentVarsWithSameName.MPS.key");
        startAutomaticStrategy(proof);
        assertTrue(proof.closed(), "automatic strategy should close the A::m proof");

        // locate the merge application
        Node mergeNode = null;
        for (Iterator<Node> it = proof.root().subtreeIterator(); it.hasNext();) {
            final Node n = it.next();
            if (n.getAppliedRuleApp() instanceof MergeRuleBuiltInRuleApp) {
                mergeNode = n;
                break;
            }
        }
        Assertions.assertNotNull(mergeNode, "expected a merge rule application in the proof");
        final Node mergeChild = mergeNode.child(0);

        // The names minted BY the merge application, clash renames among them. The merge
        // neither records its renames in the name recorder (MergeRule.apply deliberately empties
        // it mid-apply) nor in the rule app, so identify them semantically: operators occurring
        // in the merged sequent that occur neither in the merge parent's sequent nor in any
        // merge partner's sequent were introduced by the merge application itself.
        final Set<Name> before = new HashSet<>();
        collectOpNames(mergeNode.sequent(), before);
        for (MergePartner partner : ((MergeRuleBuiltInRuleApp) mergeNode.getAppliedRuleApp())
                .getMergePartners()) {
            collectOpNames(partner.getGoal().node().sequent(), before);
        }
        final Set<Name> after = new HashSet<>();
        collectOpNames(mergeChild.sequent(), after);
        final Set<Name> minted = new HashSet<>(after);
        minted.removeAll(before);
        Assertions.assertFalse(minted.isEmpty(),
            "the merge should mint symbols that occur in the merged sequent"
                + " (the A.java scenario forces at least the exc_0 clash renaming)");

        // (a) commit: each minted symbol must be reconstructible from the shared base plus the
        // node-local symbol storage -- that pair is all a namespace rebuild works from
        for (Name name : minted) {
            Assertions.assertTrue(isReconstructible(proof, mergeChild, name),
                "merge-minted symbol " + name + " occurs in the merged sequent but reaches "
                    + "neither the node-local symbol storage nor the shared namespaces; "
                    + "a namespace rebuild loses it");
        }

        // (b) prune to the merged goal: the rebuilt goal namespaces must still resolve them
        proof.pruneProof(mergeChild);
        final Goal prunedGoal = proof.getOpenGoal(mergeChild);
        Assertions.assertNotNull(prunedGoal, "pruning should reopen the merged goal");
        for (Name name : minted) {
            final boolean found =
                prunedGoal.getLocalNamespaces().functions().lookup(name) != null
                        || prunedGoal.getLocalNamespaces().programVariables()
                                .lookup(name) != null;
            Assertions.assertTrue(found,
                "merge-minted symbol " + name + " is no longer resolvable after pruning");
        }

        // (c) and the proof still closes from the pruned state
        startAutomaticStrategy(proof);
        assertTrue(proof.closed(),
            "proof should close again after pruning to the merged goal");
    }

    /**
     * Collects the names of all operators occurring in the given sequent.
     */
    private static void collectOpNames(Sequent sequent, Set<Name> into) {
        final OpCollector collector = new OpCollector();
        for (SequentFormula sf : sequent) {
            sf.formula().execPostOrder(collector);
        }
        for (Operator op : collector.ops()) {
            into.add(op.name());
        }
    }

    /**
     * Checks whether a symbol of the given name would survive a rebuild of a goal's local
     * namespaces, i.e. whether it is present in the node-local symbol storage of the given node
     * or in the proof's shared namespaces.
     */
    private static boolean isReconstructible(Proof proof, Node node, Name name) {
        for (var pv : node.getLocalProgVars()) {
            if (pv.name().equals(name)) {
                return true;
            }
        }
        for (var fun : node.getLocalFunctions()) {
            if (fun.name().equals(name)) {
                return true;
            }
        }
        final var global = proof.getServices().getNamespaces();
        return global.functions().lookup(name) != null
                || global.programVariables().lookup(name) != null;
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
     */
    @Test
    public void testDoManualGcdProof() {
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
        } catch (IncompleteRuleAppException ignored) {
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
        } catch (IncompleteRuleAppException ignored) {
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
        return loadProof(Paths.get(directory), proofFileName);
    }

    /**
     * Loads the given proof file. Checks if the proof file exists and the proof is not null, and
     * fails if the proof could not be loaded.
     *
     * @param directory directory in which the {@code proofFileName} exists
     * @param proofFileName The file name of the proof file to load.
     * @return The loaded proof.
     */
    public static @NonNull Proof loadProof(Path directory, String proofFileName) {
        Path proofFile = directory.resolve(proofFileName);
        assertTrue(Files.exists(proofFile),
            "Proof file: " + proofFile.toAbsolutePath() + " could not be found!");

        var environment = Assertions
                .assertDoesNotThrow(() -> KeYEnvironment.load(JavaProfile.getDefaultInstance(),
                    proofFile, null, null, null, true));
        Proof proof = environment.getLoadedProof();
        Assertions.assertNotNull(proof, "Loaded proof should not be null");
        var errors = environment.getReplayResult().getErrorList();
        if (!errors.isEmpty()) {
            LOGGER.warn("There were errors during load");
            for (int i = 0; i < errors.size(); i++) {
                var error = errors.get(i);
                LOGGER.warn("Error " + i + ": ", error);
            }
            Assertions.fail("There were errors during load");
        }
        return proof;
    }

    private static class IncompleteRuleAppException extends RuntimeException {
    }
}
