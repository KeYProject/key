/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing;

import java.io.File;
import java.nio.file.Files;
import java.util.concurrent.atomic.AtomicReference;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.smt.SMTRuleApp;
import de.uka.ilkd.key.util.Pair;

import org.key_project.slicing.analysis.AnalysisResults;
import org.key_project.slicing.analysis.DependencyAnalyzer;
import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Tests for the {@link DependencyTracker}, {@link DependencyAnalyzer}, ...
 *
 * @author Arne Keller
 */
class EndToEndTests {
    private static final Logger LOGGER = LoggerFactory.getLogger(EndToEndTests.class);

    public static final File testCaseDirectory = FindResources.getTestCasesDirectory();

    /**
     * Load and slice a proof after analyzing it using the dependency analysis algorithm.
     * Also checks that {@link DependencyTracker#getNodeThatProduced(Node, PosInOccurrence)} works
     * as expected.
     *
     * @throws Exception on error
     */
    @Test
    void sliceAgatha() throws Exception {
        Proof proof = sliceProof("/agatha.proof", 145, 79, true, false);

        // test getNodeThatProduced
        DependencyTracker tracker = proof.lookup(DependencyTracker.class);
        Node node26 = proof.findAny(n -> n != null && n.serialNr() == 26);
        int[] producingNodes =
            new int[] { 15, 15, 13, 12, 11, 23, 25, 24, 22, 21, 19, 17, 2, 16, 0 };
        for (int i = 0; i < producingNodes.length; i++) {
            PosInOccurrence pio = PosInOccurrence.findInSequent(
                node26.sequent(), i + 1, PosInTerm.getTopLevel());
            assertEquals(producingNodes[i],
                tracker.getNodeThatProduced(node26, pio).serialNr());
        }
    }

    /**
     * Load and slice a proof using both analysis algorithms (dependency analysis + rule app
     * de-duplication).
     * Keeps slicing until no more size improvements are possible.
     *
     * @throws Exception on error
     */
    @Test
    void sliceMultipleIterations() throws Exception {
        // simple Java proof
        Pair<Proof, File> iteration1 = sliceProofFullFilename(
            new File(testCaseDirectory,
                "../../../../../key.ui/examples/firstTouch/05-ReverseArray/reverseArray.proof"),
            6530, 4229, true, true);
        Pair<Proof, File> iteration2 =
            sliceProofFullFilename(iteration1.second, 4229, 4222, true, true);
        Pair<Proof, File> iteration3 =
            sliceProofFullFilename(iteration2.second, 4222, 4213, true, true);
        Pair<Proof, File> iteration4 =
            sliceProofFullFilename(iteration3.second, 4213, 4202, true, true);
        Pair<Proof, File> iteration5 =
            sliceProofFullFilename(iteration4.second, 4202, 4190, true, true);
        Files.delete(iteration5.second.toPath());
        Files.delete(iteration4.second.toPath());
        Files.delete(iteration3.second.toPath());
        Files.delete(iteration2.second.toPath());
        Files.delete(iteration1.second.toPath());
    }

    /**
     * Integration test of the dependency analysis algorithm on a proof related to a Java method.
     *
     * @throws Exception on error
     */
    @Test
    void sliceJavaProof() throws Exception {
        sliceProof(
            "../../../../../key.ui/examples/heap/verifyThis15_2_ParallelGcd/parallelGcd.proof",
            3238, 1336, true, false);
    }

    /**
     * Test that the dependency analyzer can remove a cut on <code>true</code>.
     *
     * @throws Exception on error
     */
    @Test
    void sliceCutExample() throws Exception {
        sliceProof("/cutExample.proof", 10, 7, true, false);
    }

    /**
     * Test that slicing works as expected on a pruned version of a real proof.
     *
     * @throws Exception on error
     */
    @Test
    void sliceAgathaWithOpenGoal() throws Exception {
        sliceProof("/agathaOpenGoal.proof", 145, 124, true, false);
    }

    /**
     * Test that slicing works as expected for simple proofs with one open goal.
     *
     * @throws Exception on error
     */
    @Test
    void sliceWithOpenGoal() throws Exception {
        sliceProof("/openGoal1.proof", 10, 7, true, false);
        sliceProof("/openGoal2.proof", 10, 7, true, false);
    }

    /**
     * Test that the branch analysis of the dependency analysis works as expected.
     * Also tests that the de-duplication analysis works as expected on this proof.
     *
     * @throws Exception on error
     */
    @Test
    void sliceIfThenElseSplit() throws Exception {
        // dependency analysis: instantly remove irrelevant steps from one branch
        sliceProof("/ifThenElseSplit.proof", 12, 6, true, false);

        // duplicate analysis: merge duplicated steps (one at a time)
        Pair<Proof, File> iteration1 = sliceProofFullFilename(
            new File(testCaseDirectory, "/ifThenElseSplit.proof"), 12, 11, false, true);
        Pair<Proof, File> iteration2 =
            sliceProofFullFilename(iteration1.second, 11, 10, false, true);
        Pair<Proof, File> iteration3 =
            sliceProofFullFilename(iteration2.second, 10, 9, false, true);
        Pair<Proof, File> iteration4 =
            sliceProofFullFilename(iteration3.second, 9, 8, false, true);
        assertEquals("w TRUE",
            iteration4.first.findAny(x -> x.serialNr() == 6).getNodeInfo().getBranchLabel());
        assertEquals("w FALSE",
            iteration4.first.findAny(x -> x.serialNr() == 7).getNodeInfo().getBranchLabel());
        Files.delete(iteration4.second.toPath());
        Files.delete(iteration3.second.toPath());
        Files.delete(iteration2.second.toPath());
        Files.delete(iteration1.second.toPath());
    }

    /**
     * Test that slicing a proof closed by SMT is possible.
     *
     * @throws Exception on error
     */
    @Test
    void sliceSimpleSMT() throws Exception {
        // only run this test if at least one SMT solver is available
        if (ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings()
                .getUsableSolverUnions(Main.isExperimentalMode()).isEmpty()) {
            return;
        }
        sliceProof("/simpleSMT.proof", 1, 1, true, false);
    }

    /**
     * Test a very specific condition in the rule application de-duplication algorithm.
     *
     * @throws Exception on error
     */
    @Test
    void deduplicateChecksMergabilityCorrectly() throws Exception {
        sliceProof("/deduplicateCheck4.proof", 19, 19, false, true);
    }

    /**
     * Test that the de-duplication algorithm works as expected for a small example.
     *
     * @throws Exception on error
     */
    @Test
    void sliceDuplicatesAway() throws Exception {
        Pair<Proof, File> iteration1 = sliceProofFullFilename(
            new File(testCaseDirectory, "/exampleDuplicate.proof"), 10, 9, false, true);
        Pair<Proof, File> iteration2 =
            sliceProofFullFilename(iteration1.second, 9, 8, false, true);
        Pair<Proof, File> iteration3 =
            sliceProofFullFilename(iteration2.second, 8, 7, false, true);
        Pair<Proof, File> iteration4 =
            sliceProofFullFilename(iteration3.second, 7, 7, false, true);
        Files.delete(iteration4.second.toPath());
        Files.delete(iteration3.second.toPath());
        Files.delete(iteration2.second.toPath());
        Files.delete(iteration1.second.toPath());
    }

    /**
     * Test that the de-duplication algorithm also works if there are open branches in the proof.
     *
     * @throws Exception on error
     */
    @Test
    void sliceDuplicatesAwayOpenGoals() throws Exception {
        Pair<Proof, File> iteration1 = sliceProofFullFilename(
            new File(testCaseDirectory, "/exampleDuplicateOpen.proof"), 10, 9, false, true);
        Pair<Proof, File> iteration2 =
            sliceProofFullFilename(iteration1.second, 9, 8, false, true);
        Pair<Proof, File> iteration3 =
            sliceProofFullFilename(iteration2.second, 8, 7, false, true);
        Pair<Proof, File> iteration4 =
            sliceProofFullFilename(iteration3.second, 7, 7, false, true);
        Files.delete(iteration4.second.toPath());
        Files.delete(iteration3.second.toPath());
        Files.delete(iteration2.second.toPath());
        Files.delete(iteration1.second.toPath());
    }

    private Proof sliceProof(String filename, int expectedTotal,
            int expectedInSlice, boolean doDependencyAnalysis, boolean doDeduplicateRuleApps)
            throws Exception {
        Pair<Proof, File> it =
            sliceProofFullFilename(new File(testCaseDirectory, filename), expectedTotal,
                expectedInSlice, doDependencyAnalysis, doDeduplicateRuleApps);
        Files.delete(it.second.toPath());
        return it.first;
    }

    private Pair<Proof, File> sliceProofFullFilename(File proofFile, int expectedTotal,
            int expectedInSlice, boolean doDependencyAnalysis,
            boolean doDeduplicateRuleApps) throws Exception {
        boolean oldValue = GeneralSettings.noPruningClosed;
        GeneralSettings.noPruningClosed = false;
        // load proof
        Assertions.assertTrue(proofFile.exists());
        AtomicReference<DependencyTracker> tracker = new AtomicReference<>();
        LOGGER.trace("Loading " + proofFile.getAbsolutePath());
        KeYEnvironment<?> environment =
            KeYEnvironment.load(JavaProfile.getDefaultInstance(), proofFile, null, null, null, null,
                null, proof -> {
                    tracker.set(new DependencyTracker(proof));
                }, true);
        try {
            // get loaded proof
            Proof proof = environment.getLoadedProof();
            Assertions.assertNotNull(proof);
            boolean originalProofClosed = proof.closed();
            // analyze proof
            AnalysisResults results =
                tracker.get().analyze(doDependencyAnalysis, doDeduplicateRuleApps);
            assertEquals(expectedTotal, results.totalSteps);
            assertEquals(expectedInSlice, results.usefulStepsNr);
            // slice proof
            DefaultUserInterfaceControl control = new DefaultUserInterfaceControl();
            SlicingProofReplayer slicer = SlicingProofReplayer.constructSlicer(control,
                proof, results, control);
            File tempFile = slicer.slice();
            KeYEnvironment<?> loadedEnvironment =
                KeYEnvironment.load(JavaProfile.getDefaultInstance(), tempFile, null, null,
                    null, null, null, DependencyTracker::new, true);
            Proof slicedProof = loadedEnvironment.getLoadedProof();

            if (originalProofClosed) {
                Assertions.assertTrue(slicedProof.closed());
            }
            assertEquals(expectedInSlice
                    + slicedProof.closedGoals().size()
                    - slicedProof.closedGoals().stream()
                            .filter(x -> x.node().getAppliedRuleApp() instanceof SMTRuleApp)
                            .count(),
                slicedProof.countNodes());

            return new Pair<>(slicedProof, tempFile);
        } finally {
            environment.dispose();
            GeneralSettings.noPruningClosed = oldValue;
        }
    }
}
