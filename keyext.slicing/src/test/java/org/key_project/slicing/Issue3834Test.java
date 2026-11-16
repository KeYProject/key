/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.slicing;

import java.nio.file.Path;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.io.ProblemLoaderControl;
import de.uka.ilkd.key.settings.GeneralSettings;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Regression test for issue #3834. The loop scope rule introduces "before" variables (e.g.
 * {@code k_before}) via {@code NewLocalVarsCondition}. These names used to carry a {@code #}-index
 * taken from a proof-global counter that is advanced as a side effect of (speculative) taclet
 * matching. The number of increments differs between a freshly created proof and one that has been
 * pruned and re-run, so the variable name changed (e.g. {@code k_before#0} vs. {@code k_before#1}),
 * which broke slicing (it relies on formula equivalence across reloads).
 * <p>
 * The scenario mirrors {@link Issue3437Test}: load the proof, prune it and re-run automode so that
 * the (previously volatile) counters would differ, then slice the proof and reload the slice.
 */
public class Issue3834Test {
    public static final Path testCaseDirectory = requireTestCasesDirectory();

    private static Path requireTestCasesDirectory() {
        Path directory = FindResources.getTestCasesDirectory();
        if (directory == null) {
            throw new NullPointerException("Test case directory not found.");
        }
        return directory;
    }

    @Test
    void loadsAndSlicesCorrectly() throws Exception {
        GeneralSettings.noPruningClosed = false;

        var file = testCaseDirectory.resolve(
            "issues/3834/SumAndMax(SumAndMax__sumAndMax((I)).JML normal_behavior operation contract.0.proof");
        var env = KeYEnvironment.load(file);
        var proof = env.getLoadedProof();
        if (proof == null) {
            throw new NullPointerException("No proof loaded for issue 3834.");
        }
        var tracker = new DependencyTracker(proof);
        ProofControl proofControl = env.getProofControl();
        if (proofControl == null) {
            throw new NullPointerException("No proof control available.");
        }
        proofControl.startAutoMode(proof, proof.openEnabledGoals());
        proofControl.waitWhileAutoMode();
        assertTrue(proof.closed());
        // prune and re-run automode so the loop scope rule is reapplied; previously this changed
        // the counter on the temporary "before" variables and thereby their names
        Node cuttingPoint = proof.findAny(x -> x.serialNr() == 13);
        if (cuttingPoint == null) {
            throw new NullPointerException("Node with serial number 13 not found.");
        }
        proof.pruneProof(cuttingPoint);
        proofControl.startAutoMode(proof, proof.openEnabledGoals());
        proofControl.waitWhileAutoMode();
        assertTrue(proof.closed());

        var results = tracker.analyze(true, false);
        if (results == null) {
            throw new NullPointerException("No analysis results returned.");
        }

        ProblemLoaderControl control = new DefaultUserInterfaceControl();
        SlicingProofReplayer replayer = SlicingProofReplayer
                .constructSlicer(control, proof, results, env.getUi());
        var newFile = replayer.slice();
        var env2 = KeYEnvironment.load(newFile);
        var proof2 = env2.getLoadedProof();
        if (proof2 == null) {
            throw new NullPointerException("No proof loaded from the sliced proof file.");
        }
        assertTrue(proof2.closed());

        env.dispose();
        env2.dispose();
        GeneralSettings.noPruningClosed = true;
    }
}
