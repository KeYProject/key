/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.mt;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.impl.ParallelProver;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.util.ProofStarter;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIfSystemProperty;

/**
 * Manual speedup/scaling benchmark for the goal-level parallel prover. <b>Not a correctness
 * gate</b>
 * — it only measures and reports; it asserts nothing. Enable with {@code -Dkey.mt.benchmark=true}
 * (skipped otherwise, because the proofs take minutes).
 *
 * <p>
 * For each large real proof it runs single-threaded automatic search (the {@code ApplyStrategy}
 * baseline, parallel prover off) and then the parallel prover at several worker counts, printing
 * wall-time, speedup, whether the proof closed, and the node count. Caveats baked into the
 * interpretation, not the run:
 * <ul>
 * <li><b>Pure automode only.</b> Driven via {@link ProofStarter}; proofs that need a proof
 * script/macro to close will simply not close here (visible as {@code closed=false} even
 * single-threaded) and are not meaningful benchmark entries.
 * <li><b>MT-disabled features.</b> {@code MergeRule} is off while a multi-worker run is active, so
 * a
 * merge-dependent proof may close single-threaded but not in parallel — the table shows this rather
 * than failing.
 * <li><b>Rough timing.</b> One run per configuration, single JVM; run with a single test fork
 * (e.g. {@code -PrapForks=1} / no parallel forks) and an otherwise idle machine, and take the
 * median
 * of a few invocations for anything you want to quote. Worker count is capped at the available
 * cores.
 * </ul>
 *
 * Worker counts come from {@code -Dkey.mt.benchmark.threads} (default {@code 1,2,4,8}); the corpus
 * from {@code -Dkey.mt.benchmark.proofs} (comma-separated example-relative paths) or a built-in
 * default set of large automode proofs.
 *
 * @author Claude (KeY multithreading effort)
 */
@EnabledIfSystemProperty(named = "key.mt.benchmark", matches = "true")
public class MtSpeedupBenchmark {

    /**
     * Default corpus: large, automode-closeable, script-free real proofs (a {@code perfTest}-style
     * set). Entries that do not close under pure automode show {@code closed=false} in the table
     * and
     * are not meaningful speedup entries — curate via {@code -Dkey.mt.benchmark.proofs} as needed.
     */
    private static final String[] DEFAULT_PROOFS = {
        "newBook/09.list_modelfield/ArrayList.remFirst.key",
        "standard_key/java_dl/symmArray.key",
        "heap/saddleback_search/Saddleback_search.key",
        "heap/list_seq/SimplifiedLinkedList.remove.key",
    };

    /**
     * Clean snapshot of the global proof settings, captured before any proof is loaded. Loading a
     * {@code .key}/{@code .proof} mutates {@link ProofSettings#DEFAULT_SETTINGS}; without restoring
     * it before each proof, a proof would inherit the previous corpus entry's strategy settings and
     * may take a different (or non-closing) search path -- making per-proof numbers depend on
     * corpus
     * order. {@link #run} restores this snapshot before every load.
     */
    private static String settingsBaseline;

    @Test
    void benchmark() throws Exception {
        Path examples = FindResources.getExampleDirectory();
        if (examples == null) {
            System.out.println("[mt-benchmark] examples directory not found; nothing to do");
            return;
        }
        settingsBaseline = ProofSettings.DEFAULT_SETTINGS.settingsToString();
        int cores = Runtime.getRuntime().availableProcessors();
        List<Integer> workerCounts = workerCounts(cores);
        String[] proofs = System.getProperty("key.mt.benchmark.proofs", "").isBlank()
                ? DEFAULT_PROOFS
                : System.getProperty("key.mt.benchmark.proofs").split("\\s*,\\s*");

        System.out.printf("%n[mt-benchmark] cores=%d worker-counts=%s%n", cores, workerCounts);
        System.out.printf("%-52s %10s %8s %7s %s%n", "proof", "config", "time(ms)", "speedup",
            "closed/nodes");

        // Paste-ready markdown table for the pull-request descriptions, accumulated alongside the
        // human-readable output above.
        StringBuilder md = new StringBuilder("\n[mt-benchmark-markdown]\n| # | Proof | main (s) |");
        for (int w : workerCounts) {
            md.append(' ').append(w).append("× |");
        }
        md.append("\n|---|---|---|");
        for (int i = 0; i < workerCounts.size(); i++) {
            md.append("---|");
        }
        md.append('\n');

        int row = 0;
        for (String rel : proofs) {
            Path keyFile = examples.resolve(rel);
            if (!Files.exists(keyFile)) {
                System.out.printf("%-52s  (missing)%n", rel);
                continue;
            }
            run(keyFile, 0); // warm-up (untimed): JIT-compile this proof's code paths so the
                             // single-threaded baseline below is not penalised by cold compilation.
            Run base = run(keyFile, 0); // single-threaded ApplyStrategy baseline
            System.out.printf("%-52s %10s %8d %7s %s/%d%n", shortName(rel), "single", base.millis,
                "1.00x", base.closed, base.nodes);
            md.append("| ").append(++row).append(" | ").append(shortName(rel)).append(" | ")
                    .append(String.format("%.1f", base.millis / 1000.0)).append(" |");
            for (int w : workerCounts) {
                Run r = run(keyFile, w);
                double speedup = r.millis > 0 ? (double) base.millis / r.millis : 0.0;
                String why = r.closed ? "" : "  [open=" + r.openGoals + " reason=" + r.reason + "]";
                System.out.printf("%-52s %10s %8d %6.2fx %s/%d%s%n", "", w + "-worker", r.millis,
                    speedup, r.closed, r.nodes, why);
                md.append(String.format(" %.2f× |", speedup));
            }
            md.append('\n');
        }
        System.out.println(md);
    }

    private static List<Integer> workerCounts(int cores) {
        String prop = System.getProperty("key.mt.benchmark.threads", "1,2,4,8");
        List<Integer> result = new ArrayList<>();
        for (String s : prop.split("\\s*,\\s*")) {
            int w = Math.min(Integer.parseInt(s.trim()), cores);
            if (!result.contains(w)) {
                result.add(w);
            }
        }
        return result;
    }

    /** Runs one proof; {@code workers == 0} means the single-threaded baseline (parallel off). */
    private static Run run(Path keyFile, int workers) throws Exception {
        // Isolate each proof from the previous one's settings (see settingsBaseline).
        if (settingsBaseline != null) {
            ProofSettings.DEFAULT_SETTINGS.loadSettingsFromPropertyString(settingsBaseline);
        }
        KeYEnvironment<?> env = KeYEnvironment.load(keyFile);
        String prevEnabled = System.getProperty(ParallelProver.PARALLEL_PROPERTY);
        String prevThreads = System.getProperty(ParallelProver.THREADS_PROPERTY);
        if (workers > 0) {
            System.setProperty(ParallelProver.PARALLEL_PROPERTY, "true");
            System.setProperty(ParallelProver.THREADS_PROPERTY, Integer.toString(workers));
        } else {
            // Force true sequential. Clearing is NOT enough: an unset property falls back to the
            // persisted general setting (ParallelProver.isEnabled()), which may be parallel-on, so
            // the "single" baseline would secretly run parallel. Set it explicitly to false.
            System.setProperty(ParallelProver.PARALLEL_PROPERTY, "false");
        }
        try {
            Proof proof = env.getLoadedProof();
            ProofStarter starter = new ProofStarter(false);
            starter.init(proof);
            // Optional step-budget override: some proofs need more rule applications than the
            // proof's stored strategy budget to close in pure automode
            // (-Dkey.mt.benchmark.maxsteps).
            String maxStepsProp = System.getProperty("key.mt.benchmark.maxsteps");
            if (maxStepsProp != null && !maxStepsProp.isBlank()) {
                starter.setMaxRuleApplications(Integer.parseInt(maxStepsProp.trim()));
            }
            long t0 = System.nanoTime();
            var info = starter.start();
            long millis = (System.nanoTime() - t0) / 1_000_000L;
            return new Run(millis, proof.closed(), proof.countNodes(),
                proof.openGoals().size(), info.reason());
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

    private static String shortName(String rel) {
        int slash = rel.lastIndexOf('/');
        return slash >= 0 ? rel.substring(slash + 1) : rel;
    }

    private record Run(long millis, boolean closed, int nodes, int openGoals, String reason) {
    }
}
