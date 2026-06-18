/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.mt;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.impl.ParallelProver;
import de.uka.ilkd.key.util.ProofStarter;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIfSystemProperty;

/**
 * A focused driver that runs <em>only</em> the goal-level parallel prover on a single proof, with
 * no
 * warm-up and no single-threaded baseline, so that a Flight Recording of the test JVM captures the
 * parallel run cleanly. Used to investigate the parallel prover's lock contention/hot paths and the
 * nondeterministic non-closure race (a goal whose {@code next()} returns null spuriously at &gt;1
 * worker). Enable with {@code -Dkey.mt.jfr.probe=true}; record with {@code -Dkey.mt.jfr=<file>}.
 *
 * <p>
 * Knobs: {@code -Dkey.mt.jfr.proof} (example-relative path, default symmArray),
 * {@code -Dkey.mt.jfr.workers} (default 2), {@code -Dkey.mt.jfr.reps} (default 1). Run several reps
 * to raise the odds of capturing a failing (non-closing) run; each rep prints
 * closed/open/nodes/reason so the recording can be correlated with an outcome.
 *
 * @author Claude (KeY multithreading effort)
 */
@EnabledIfSystemProperty(named = "key.mt.jfr.probe", matches = "true")
public class MtJfrProbe {

    @Test
    void run() throws Exception {
        final String rel =
            System.getProperty("key.mt.jfr.proof", "standard_key/java_dl/symmArray.key");
        final int workers = Integer.getInteger("key.mt.jfr.workers", 2);
        final int reps = Integer.getInteger("key.mt.jfr.reps", 1);

        final Path examples = FindResources.getExampleDirectory();
        if (examples == null) {
            System.out.println("[jfr-probe] examples directory not found; nothing to do");
            return;
        }
        final Path keyFile = examples.resolve(rel);
        if (!Files.exists(keyFile)) {
            System.out.printf("[jfr-probe] missing proof %s%n", rel);
            return;
        }

        System.setProperty(ParallelProver.PARALLEL_PROPERTY, "true");
        System.setProperty(ParallelProver.THREADS_PROPERTY, Integer.toString(workers));
        System.out.printf("[jfr-probe] proof=%s workers=%d reps=%d%n", rel, workers, reps);

        int failures = 0;
        for (int i = 0; i < reps; i++) {
            KeYEnvironment<?> env = KeYEnvironment.load(keyFile);
            try {
                Proof proof = env.getLoadedProof();
                ProofStarter starter = new ProofStarter(false);
                starter.init(proof);
                long t0 = System.nanoTime();
                var info = starter.start();
                long millis = (System.nanoTime() - t0) / 1_000_000L;
                boolean closed = proof.closed();
                if (!closed) {
                    failures++;
                }
                System.out.printf(
                    "[jfr-probe] rep=%d closed=%s open=%d nodes=%d time=%dms reason=%s%n",
                    i, closed, proof.openGoals().size(), proof.countNodes(), millis, info.reason());
            } finally {
                env.dispose();
            }
        }
        System.out.printf("[jfr-probe] done: %d/%d runs did NOT close%n", failures, reps);
    }
}
