/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing;

import java.nio.file.Path;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.io.ProblemLoaderControl;
import de.uka.ilkd.key.settings.GeneralSettings;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertTrue;

public class Issue3437Test {
    public static final Path testCaseDirectory = FindResources.getTestCasesDirectory();

    @Test
    void loadsAndSlicesCorrectly() throws Exception {
        GeneralSettings.noPruningClosed = false;

        var file = testCaseDirectory.resolve(
            "issues/3437/Newnames(Newnames__createArray()).JML normal_behavior operation contract.0.proof");
        var env = KeYEnvironment.load(file);
        var proof = env.getLoadedProof();
        var tracker = new DependencyTracker(proof);
        env.getProofControl().startAutoMode(proof, proof.openEnabledGoals());
        env.getProofControl().waitWhileAutoMode();
        assertTrue(proof.closed());
        // prune and re-run automode to ensure the counters on the temporary variables are different
        proof.pruneProof(proof.findAny(x -> x.serialNr() == 13));
        env.getProofControl().startAutoMode(proof, proof.openEnabledGoals());
        env.getProofControl().waitWhileAutoMode();
        assertTrue(proof.closed());

        var results = tracker.analyze(true, false);

        ProblemLoaderControl control = new DefaultUserInterfaceControl();
        SlicingProofReplayer replayer = SlicingProofReplayer
                .constructSlicer(control, proof, results, env.getUi());
        var newFile = replayer.slice();
        var env2 = KeYEnvironment.load(newFile);
        var proof2 = env.getLoadedProof();
        assertTrue(proof2.closed());

        env.dispose();
        env2.dispose();
        GeneralSettings.noPruningClosed = true;
    }
}
