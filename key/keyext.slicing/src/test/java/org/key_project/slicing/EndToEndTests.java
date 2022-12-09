package org.key_project.slicing;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.util.Pair;
import org.junit.Ignore;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.key_project.util.helper.FindResources;

import java.io.File;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.concurrent.atomic.AtomicReference;

/**
 * Tests for the {@link DependencyTracker}, {@link DependencyAnalyzer}, {@link ProofSlicer}, ...
 *
 * @author Arne Keller
 */
class EndToEndTests {
    public static final File testCaseDirectory = FindResources.getTestCasesDirectory();

    // TODO tests for: proof pruning, dot export, getNodeThatProduced, running both algorithms...

    @Test
    void sliceAgatha() throws Exception {
        sliceProof("/agatha.proof", 145, 79, 79, true, false);
    }

    @Test
    void sliceRemoveDuplicates() throws Exception {
        // simple Java proof
        sliceProof("/removeDuplicates.zproof", 4960, 2467, 2467, true, false);
    }

    @Test
    void sliceSitaRearrange() throws Exception {
        // this test case requires One Step Simplifactions to be restricted when slicing the proof
        Assertions.assertFalse(OneStepSimplifier.disableOSSRestriction);
        sliceProof("/sitaRearrange.zproof", 2722, 2162, 2162, true, false);
    }

    @Test
    void sliceCutExample() throws Exception {
        sliceProof("/cutExample.proof", 10, 7, 7, true, false);
    }

    @Test
    @Ignore // until this feature is implemented
    void sliceWithOpenGoal1() throws Exception {
        sliceProof("/openGoal1.proof", 9, 8, 8, true, false);
    }

    @Test
    @Ignore // until this feature is implemented
    void sliceWithOpenGoal2() throws Exception {
        sliceProof("/openGoal2.proof", 9, 8, 8, true, false);
    }

    @Test
    void sliceIfThenElseSplit() throws Exception {
        sliceProof("/ifThenElseSplit.proof", 12, 6, 6, true, false);
    }

    @Test
    void sliceSimpleSMT() throws Exception {
        sliceProof("/simpleSMT.proof", 1, 1, 0, true, false);
    }

    @Test
    void sliceDuplicatesAway() throws Exception {
        var iteration1 = sliceProofFullFilename(
            new File(testCaseDirectory, "/exampleDuplicate.proof"), 10, 9, 9, false, true);
        var iteration2 = sliceProofFullFilename(iteration1.second, 9, 8, 8, false, true);
        var iteration3 = sliceProofFullFilename(iteration2.second, 8, 7, 7, false, true);
        var iteration4 = sliceProofFullFilename(iteration3.second, 7, 7, 7, false, true);
        Files.delete(iteration4.second.toPath());
        Files.delete(iteration3.second.toPath());
        Files.delete(iteration2.second.toPath());
        Files.delete(iteration1.second.toPath());
    }

    private Proof sliceProof(String filename, int expectedTotal, int expectedUseful,
            int expectedInSlice, boolean doDependencyAnalysis, boolean doDeduplicateRuleApps)
            throws Exception {
        var it = sliceProofFullFilename(new File(testCaseDirectory, filename), expectedTotal,
            expectedUseful, expectedInSlice, doDependencyAnalysis, doDeduplicateRuleApps);
        Files.delete(it.second.toPath());
        return it.first;
    }

    private Pair<Proof, File> sliceProofFullFilename(File proofFile, int expectedTotal,
            int expectedUseful, int expectedInSlice, boolean doDependencyAnalysis,
            boolean doDeduplicateRuleApps) throws Exception {
        boolean oldValue = GeneralSettings.noPruningClosed;
        GeneralSettings.noPruningClosed = false;
        // load proof
        Assertions.assertTrue(proofFile.exists());
        AtomicReference<DependencyTracker> tracker = new AtomicReference<>();
        System.out.println("loading " + proofFile.getAbsolutePath());
        KeYEnvironment<?> environment =
            KeYEnvironment.load(JavaProfile.getDefaultInstance(), proofFile, null, null, null, null,
                null, proof -> {
                    tracker.set(new DependencyTracker(proof));
                    proof.addRuleAppListener(tracker.get());
                }, true);
        try {
            // get loaded proof
            Proof proof = environment.getLoadedProof();
            Assertions.assertNotNull(proof);
            // analyze proof
            var results = tracker.get().analyze(doDependencyAnalysis, doDeduplicateRuleApps);
            Assertions.assertEquals(expectedTotal, results.totalSteps);
            Assertions.assertEquals(expectedUseful, results.usefulStepsNr);
            // slice proof
            // var path = tracker.sliceProof();
            // var env2 = KeYEnvironment.load(JavaProfile.getDefaultInstance(), path.toFile(), null,
            // null, null, null, null, null, true);
            // try {
            var control = new DefaultUserInterfaceControl();
            var slicer = SlicingProofReplayer.constructSlicer(control,
                proof, results, control);
            File tempFile = slicer.slice();
            KeYEnvironment<?> loadedEnvironment =
                KeYEnvironment.load(JavaProfile.getDefaultInstance(), tempFile, null, null,
                    null, null, null, null, true);
            try {
                Proof slicedProof = loadedEnvironment.getLoadedProof();

                Assertions.assertTrue(slicedProof.closed());
                Assertions.assertEquals(expectedInSlice + slicedProof.closedGoals().size(),
                    slicedProof.countNodes());

                return new Pair<>(slicedProof, tempFile);
            } finally {
                loadedEnvironment.dispose();
            }
            // } finally {
            // env2.dispose();
            // }
        } finally {
            environment.dispose();
            GeneralSettings.noPruningClosed = oldValue;
        }
    }
}
