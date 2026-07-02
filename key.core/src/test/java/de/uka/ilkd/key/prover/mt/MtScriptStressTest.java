/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.mt;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.prover.impl.ParallelProver;
import de.uka.ilkd.key.scripts.ProofScriptEngine;
import de.uka.ilkd.key.settings.ProofSettings;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIfSystemProperty;

import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Stress test: a real, position-sensitive proof script must still close the proof when the
 * multi-core prover is active.
 *
 * <p>
 * The quicksort {@code sort.script} is the worst case for parallel execution: it runs a
 * parallel-capable {@code macro "autopilot-prep"} and then applies literal
 * {@code select}/{@code rule formula="..."} commands that reference fresh names (e.g.
 * {@code heapAfter_sort_0}) introduced by that macro. If a parallel run reordered goals or
 * worker-tagged those fresh names, the later literal commands would fail to apply and the script
 * would not close. This pins that scripts keep working under the multi-core prover.
 *
 * <p>
 * Gated behind {@code -Dkey.mt.stress=true} (slow: runs the autopilot preparation several times)
 * and
 * executed by the {@code testMtStress} Gradle task, alongside {@link MtStressTest} and
 * {@link MtMacroStressTest}.
 */
@EnabledIfSystemProperty(named = "key.mt.stress", matches = "true")
public class MtScriptStressTest {

    /**
     * Loading the quicksort example applies its embedded settings to the global
     * {@link ProofSettings#DEFAULT_SETTINGS}; snapshot and restore them so they do not leak into
     * every proof loaded later in the same JVM (and each repetition here starts identically).
     */
    private static String settingsSnapshot;

    @BeforeAll
    static void snapshotSettings() {
        settingsSnapshot = ProofSettings.DEFAULT_SETTINGS.settingsToString();
    }

    @AfterAll
    static void restoreSettings() {
        ProofSettings.DEFAULT_SETTINGS.loadSettingsFromPropertyString(settingsSnapshot);
    }


    /**
     * Over-subscribed worker count to maximise interleaving (the machine need not have this many).
     */
    private static final int MT_WORKERS = 8;
    /** Number of multi-core repetitions; a race would surface as an occasional non-closure. */
    private static final int MT_REPS = 3;

    @Test
    void sortScriptClosesUnderMultiCore() throws Exception {
        Path examples = FindResources.getExampleDirectory();
        Path keyFile = examples.resolve("heap/quicksort/sort.key");
        String scriptText = Files.readString(examples.resolve("heap/quicksort/sort.script"));

        // Baseline: the script must close on the single-core prover.
        assertTrue(runScript(scriptText, keyFile, 0),
            "sort.script did not close on the single-core prover");

        // It must also close on every multi-core run, despite the parallel macro and the literal
        // name references that follow it.
        for (int rep = 1; rep <= MT_REPS; rep++) {
            assertTrue(runScript(scriptText, keyFile, MT_WORKERS),
                "sort.script did not close on the multi-core prover (run " + rep + " of " + MT_REPS
                    + ")");
        }
    }

    /**
     * A proof produced under the multi-core prover (with worker-tagged fresh names and a
     * parallel-explored tree) must save and reload as a valid, closed proof under the single-core
     * prover -- i.e. the saved artifact carries no multi-core-specific corruption and replays
     * exactly like any other proof.
     */
    @Test
    void multiCoreProofSavesAndReloadsSingleCore() throws Exception {
        Path examples = FindResources.getExampleDirectory();
        Path keyFile = examples.resolve("heap/quicksort/sort.key");
        String scriptText = Files.readString(examples.resolve("heap/quicksort/sort.script"));
        // Save next to sort.key so the proof's relative \javaSource "." resolves on reload.
        Path saved = Files.createTempFile(keyFile.getParent(), "mt-sort-proof", ".proof");

        // 1) Produce the proof under the multi-core prover, then save it.
        ProofSettings.DEFAULT_SETTINGS.loadSettingsFromPropertyString(settingsSnapshot);
        System.setProperty(ParallelProver.PARALLEL_PROPERTY, "true");
        System.setProperty(ParallelProver.THREADS_PROPERTY, Integer.toString(MT_WORKERS));
        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(keyFile);
        try {
            Proof proof = env.getLoadedProof();
            new ProofScriptEngine(proof).execute(env.getUi(),
                ParsingFacade.parseScript(scriptText));
            assertTrue(proof.closed(), "the multi-core proof did not close before saving");
            String status = new ProofSaver(proof, saved).save();
            assertTrue(status == null || status.isEmpty(),
                "saving the multi-core proof reported an error: " + status);
        } finally {
            System.clearProperty(ParallelProver.PARALLEL_PROPERTY);
            System.clearProperty(ParallelProver.THREADS_PROPERTY);
            env.dispose();
        }

        // 2) Reload it with the single-core prover; it must load cleanly and still be closed.
        ProofSettings.DEFAULT_SETTINGS.loadSettingsFromPropertyString(settingsSnapshot);
        KeYEnvironment<DefaultUserInterfaceControl> reloadEnv = KeYEnvironment.load(saved);
        try {
            Proof reloaded = reloadEnv.getLoadedProof();
            assertNotNull(reloaded, "reloading the saved multi-core proof produced no proof");
            assertTrue(reloaded.closed(),
                "the saved multi-core proof did not reload as a closed proof");
        } finally {
            reloadEnv.dispose();
            Files.deleteIfExists(saved);
        }
    }

    /**
     * Loads the proof obligation fresh, runs the proof script, and reports whether the proof
     * closed.
     *
     * @param scriptText the proof script to execute
     * @param keyFile the proof obligation to load
     * @param workers {@code 0} for the single-core prover, otherwise the parallel worker count
     * @return whether the proof is closed after the script ran
     */
    private static boolean runScript(String scriptText, Path keyFile, int workers)
            throws Exception {
        String prevEnabled = System.getProperty(ParallelProver.PARALLEL_PROPERTY);
        String prevThreads = System.getProperty(ParallelProver.THREADS_PROPERTY);
        if (workers > 0) {
            System.setProperty(ParallelProver.PARALLEL_PROPERTY, "true");
            System.setProperty(ParallelProver.THREADS_PROPERTY, Integer.toString(workers));
        } else {
            System.clearProperty(ParallelProver.PARALLEL_PROPERTY);
        }
        ProofSettings.DEFAULT_SETTINGS.loadSettingsFromPropertyString(settingsSnapshot);
        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(keyFile);
        try {
            Proof proof = env.getLoadedProof();
            var script = ParsingFacade.parseScript(scriptText);
            new ProofScriptEngine(proof).execute(env.getUi(), script);
            return proof.closed();
        } finally {
            restore(ParallelProver.PARALLEL_PROPERTY, prevEnabled);
            restore(ParallelProver.THREADS_PROPERTY, prevThreads);
            env.dispose();
        }
    }

    private static void restore(String key, String previous) {
        if (previous == null) {
            System.clearProperty(key);
        } else {
            System.setProperty(key, previous);
        }
    }
}
