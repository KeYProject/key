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
    public static final Path testCaseDirectory = FindResources.getTestCasesDirectory();

    @Test
    void loadsAndSlicesCorrectly() throws Exception {
        GeneralSettings.noPruningClosed = false;

        var file = testCaseDirectory.resolve(
            "issues/3834/SumAndMax(SumAndMax__sumAndMax((I)).JML normal_behavior operation contract.0.proof");
        var env = KeYEnvironment.load(file);
        var proof = env.getLoadedProof();
        var tracker = new DependencyTracker(proof);
        env.getProofControl().startAutoMode(proof, proof.openEnabledGoals());
        env.getProofControl().waitWhileAutoMode();
        assertTrue(proof.closed());
        // prune and re-run automode so the loop scope rule is reapplied; previously this changed
        // the counter on the temporary "before" variables and thereby their names
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
        var proof2 = env2.getLoadedProof();
        assertTrue(proof2.closed());

        env.dispose();
        env2.dispose();
        GeneralSettings.noPruningClosed = true;
    }
}
