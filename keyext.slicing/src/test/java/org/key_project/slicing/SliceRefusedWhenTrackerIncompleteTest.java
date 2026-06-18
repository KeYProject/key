/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing;

import java.nio.file.Path;
import java.util.concurrent.atomic.AtomicReference;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.settings.GeneralSettings;

import org.key_project.slicing.analysis.AnalysisResults;
import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Regression test for the multi-core/slicing fail-safe. Proof slicing is single-core only: enabling
 * the multi-core prover suspends the (non-essential) {@link DependencyTracker} for the duration of
 * each run, so the tracker silently misses those rules and its dependency graph develops a gap.
 * {@link SlicingExtension} then marks the tracker incomplete via
 * {@link DependencyTracker#markIncompleteAfterParallelRun()}; after that, {@link
 * DependencyTracker#analyze} must refuse to return a slice so one can never be built from the
 * partial graph (which would otherwise produce an unsound/broken sliced proof).
 */
public class SliceRefusedWhenTrackerIncompleteTest {
    private static final Path testCaseDirectory = FindResources.getTestCasesDirectory();

    @Test
    void analyzeRefusesAfterTrackerMarkedIncomplete() throws Exception {
        final boolean oldValue = GeneralSettings.noPruningClosed;
        GeneralSettings.noPruningClosed = false;
        final AtomicReference<DependencyTracker> tracker = new AtomicReference<>();
        final KeYEnvironment<?> env = KeYEnvironment.load(JavaProfile.getDefaultInstance(),
            testCaseDirectory.resolve("cutExample.proof"), null, null, null, null, null,
            proof -> tracker.set(new DependencyTracker(proof)), true);
        try {
            final Proof proof = env.getLoadedProof();
            assertTrue(proof.closed(), "the loaded example proof is closed");

            // a complete tracker yields a slice
            final AnalysisResults before = tracker.get().analyze(true, false);
            assertNotNull(before, "a complete tracker must yield analysis results");

            // simulate the multi-core prover having suspended this listener for a run
            tracker.get().markIncompleteAfterParallelRun();
            assertNull(tracker.get().analyze(true, false),
                "a slice must be refused once the dependency graph is known incomplete");
        } finally {
            env.dispose();
            GeneralSettings.noPruningClosed = oldValue;
        }
    }
}
