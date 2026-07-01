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
 * Run-to-run proof-size <b>variance</b> probe for the goal-level parallel prover. Not a correctness
 * gate -- it measures and prints, it asserts nothing. Enable with {@code -Dkey.mt.variance=true}
 * (skipped otherwise, because it proves the same proof many times and takes minutes).
 *
 * <p>
 * For each proof and worker count it proves the same proof {@code reps} times and reports the
 * spread
 * (max-min), mean and stddev of both the node count and the total rule-app count. The sequential
 * reference ({@code w=0}) is deterministic (spread 0); any spread at {@code w>0} is the parallel
 * prover's goal-order sensitivity. Used to check that the thread-safety fixes (shared-cache races
 * in
 * LexPathOrdering, the quantifier heuristics, ModalityCache and the block/loop contract memos) did
 * not inflate -- and ideally reduced -- run-to-run variance. This generalises the earlier
 * 10-rep/single-proof {@code ArithVariance} form.
 *
 * <p>
 * Knobs (all {@code key.mt.variance.*}, forwarded to the test JVM by the build's {@code key.*}
 * passthrough): {@code reps} (default 20), {@code threads} (default {@code "0,2,4,8"}),
 * {@code proofs} (comma-separated example-relative paths, default the arith {@code add} proof),
 * {@code maxsteps} (default 200000). Worker counts are capped at the available cores. Run isolated:
 *
 * <pre>
 * ./gradlew :key.core:test --tests '*MtVarianceBenchmark' -Dkey.mt.variance=true --rerun-tasks
 * </pre>
 *
 * @author Claude (KeY multithreading effort)
 */
@EnabledIfSystemProperty(named = "key.mt.variance", matches = "true")
public class MtVarianceBenchmark {

    private static final String DEFAULT_PROOF = "standard_key/arith/gemplusDecimal/add.key";

    /**
     * Clean snapshot of the global proof settings, captured before any proof is loaded. Loading a
     * {@code .key} mutates {@link ProofSettings#DEFAULT_SETTINGS}; restoring the snapshot before
     * every load keeps every repetition identical (and isolates proofs from each other).
     */
    private String settingsBaseline;

    @Test
    void measure() throws Exception {
        Path examples = FindResources.getExampleDirectory();
        if (examples == null) {
            System.out.println("[mt-variance] examples directory not found; nothing to do");
            return;
        }
        settingsBaseline = ProofSettings.DEFAULT_SETTINGS.settingsToString();
        final int reps = Integer.getInteger("key.mt.variance.reps", 20);
        final int maxSteps = Integer.getInteger("key.mt.variance.maxsteps", 200000);
        final int cores = Runtime.getRuntime().availableProcessors();
        final List<Integer> workers = caps(System.getProperty("key.mt.variance.threads", "0,2,4,8"),
            cores);
        final String[] proofs = System.getProperty("key.mt.variance.proofs", "").isBlank()
                ? new String[] { DEFAULT_PROOF }
                : System.getProperty("key.mt.variance.proofs").split("\\s*,\\s*");

        System.out.printf("%n[mt-variance] cores=%d reps=%d worker-caps=%s maxsteps=%d%n",
            cores, reps, workers, maxSteps);

        for (String rel : proofs) {
            final Path keyFile = examples.resolve(rel);
            if (!Files.exists(keyFile)) {
                System.out.printf("MVAR %-24s (missing)%n", rel);
                continue;
            }
            // Untimed warm-up (not recorded): JIT-compile this proof's paths, including the
            // parallel ones, so the first recorded repetition is not an outlier.
            final int warm = workers.stream().mapToInt(Integer::intValue).max().orElse(0);
            prove(keyFile, warm, maxSteps);

            for (final int w : workers) {
                final long[] nodes = new long[reps];
                final long[] apps = new long[reps];
                boolean allClosed = true;
                for (int i = 0; i < reps; i++) {
                    final int[] r = prove(keyFile, w, maxSteps);
                    nodes[i] = r[0];
                    apps[i] = r[1];
                    allClosed &= r[2] == 1;
                }
                report(shortName(rel), w, "nodes", nodes, allClosed);
                report(shortName(rel), w, "ruleapps", apps, allClosed);
            }
        }
    }

    /** Proves {@code keyFile} once; {@code workers == 0} means the deterministic sequential run. */
    private int[] prove(Path keyFile, int workers, int maxSteps) throws Exception {
        if (settingsBaseline != null) {
            ProofSettings.DEFAULT_SETTINGS.loadSettingsFromPropertyString(settingsBaseline);
        }
        final String prevEnabled = System.getProperty(ParallelProver.PARALLEL_PROPERTY);
        final String prevThreads = System.getProperty(ParallelProver.THREADS_PROPERTY);
        if (workers > 0) {
            System.setProperty(ParallelProver.PARALLEL_PROPERTY, "true");
            System.setProperty(ParallelProver.THREADS_PROPERTY, Integer.toString(workers));
        } else {
            // Force true sequential: an unset flag falls back to the persisted general setting.
            System.setProperty(ParallelProver.PARALLEL_PROPERTY, "false");
        }
        final KeYEnvironment<?> env = KeYEnvironment.load(keyFile);
        try {
            final Proof proof = env.getLoadedProof();
            final ProofStarter starter = new ProofStarter(false);
            starter.init(proof);
            if (maxSteps > 0) {
                starter.setMaxRuleApplications(maxSteps);
            }
            starter.start();
            return new int[] { proof.countNodes(), proof.getStatistics().totalRuleApps,
                proof.closed() ? 1 : 0 };
        } finally {
            restore(ParallelProver.PARALLEL_PROPERTY, prevEnabled);
            restore(ParallelProver.THREADS_PROPERTY, prevThreads);
            env.dispose();
        }
    }

    private static void report(String proof, int workers, String metric, long[] xs,
            boolean allClosed) {
        long min = Long.MAX_VALUE;
        long max = Long.MIN_VALUE;
        long sum = 0;
        for (final long x : xs) {
            min = Math.min(min, x);
            max = Math.max(max, x);
            sum += x;
        }
        final double mean = (double) sum / xs.length;
        double sqDev = 0;
        for (final long x : xs) {
            sqDev += (x - mean) * (x - mean);
        }
        final double sd = Math.sqrt(sqDev / xs.length);
        final StringBuilder vals = new StringBuilder();
        for (final long x : xs) {
            vals.append(' ').append(x);
        }
        System.out.printf(
            "MVAR %-24s w=%-2d %-9s spread=%-6d min=%-7d max=%-7d mean=%-9.1f sd=%-7.2f closed=%b"
                + " vals:%s%n",
            proof, workers, metric, (max - min), min, max, mean, sd, allClosed, vals);
    }

    private static List<Integer> caps(String csv, int cores) {
        final List<Integer> out = new ArrayList<>();
        for (final String s : csv.split("\\s*,\\s*")) {
            final int w = Integer.parseInt(s.trim());
            final int cap = w <= 0 ? 0 : Math.min(w, cores);
            if (!out.contains(cap)) {
                out.add(cap);
            }
        }
        return out;
    }

    private static void restore(String key, String previous) {
        if (previous == null) {
            System.clearProperty(key);
        } else {
            System.setProperty(key, previous);
        }
    }

    private static String shortName(String rel) {
        final int slash = rel.lastIndexOf('/');
        return slash >= 0 ? rel.substring(slash + 1) : rel;
    }
}
