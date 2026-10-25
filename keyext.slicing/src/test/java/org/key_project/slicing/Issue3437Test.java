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

public class Issue3437Test {
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
            "issues/3437/Newnames(Newnames__createArray()).JML normal_behavior operation contract.0.proof");
        var env = KeYEnvironment.load(file);
        var proof = env.getLoadedProof();
        if (proof == null) {
            throw new NullPointerException("No proof loaded for issue 3437.");
        }
        var tracker = new DependencyTracker(proof);
        ProofControl proofControl = env.getProofControl();
        if (proofControl == null) {
            throw new NullPointerException("No proof control available.");
        }
        proofControl.startAutoMode(proof, proof.openEnabledGoals());
        proofControl.waitWhileAutoMode();
        assertTrue(proof.closed());
        // prune and re-run automode to ensure the counters on the temporary variables are different
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
