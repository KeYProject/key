/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.mtprobe.driver;

import java.nio.file.Path;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.mtprobe.DivergenceReport;
import de.uka.ilkd.key.mtprobe.ProbeRun;
import de.uka.ilkd.key.mtprobe.ProbeSink;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.impl.ParallelProver;
import de.uka.ilkd.key.util.ProofStarter;

import org.key_project.prover.rules.RuleApp;

/**
 * Runs one proof single-core once (the baseline) and then several times on the multi-core prover,
 * and prints where the multi-core runs diverge from the baseline.
 * <p>
 * It records one built-in comparison site itself, {@code proof-tree}: every node of the finished
 * proof, keyed by its position in the tree with sibling branches sorted into a canonical order (so
 * the legitimate reordering of independent branches is not counted as a difference), with the
 * applied rule as the value. Any further sites (for example {@code choice-point}) are woven in by
 * the agent; this driver just starts and stops the recording around each proof.
 * <p>
 * Usage: {@code DivergenceDriver <proof.key> [workers=4,8] [reps=200]}
 */
public final class DivergenceDriver {

    private static final String PROOF_TREE = "proof-tree";

    public static void main(String[] args) throws Exception {
        if (args.length < 1) {
            System.err.println("usage: DivergenceDriver <proof.key> [workers=4,8] [reps=200]");
            System.exit(2);
        }
        final Path keyFile = Path.of(args[0]);
        int[] workers = { 4, 8 };
        int reps = 200;
        for (int i = 1; i < args.length; i++) {
            if (args[i].startsWith("workers=")) {
                workers = parseInts(args[i].substring("workers=".length()));
            } else if (args[i].startsWith("reps=")) {
                reps = Integer.parseInt(args[i].substring("reps=".length()));
            }
        }
        // the proof-tree site is always on; the agent may have turned on more
        ProbeSink.enableSites(PROOF_TREE);
        System.out.println("mt-probe: proof=" + keyFile + " workers=" + java.util.Arrays.toString(workers)
            + " reps/worker=" + reps + " sites=" + ProbeSink.enabledSites());

        final ProbeRun baseline = proveInto("single-core", keyFile, false, 0);
        System.out.println("baseline: fullyClosed=" + !baseline.observations().containsValue("<open>")
            + " proof-tree keys=" + baseline.observations().size()
            + " violations=" + baseline.violations().size()
            + " warnings=" + baseline.warnings().size() + " (warnings are latent risks, not bugs)");

        int divergedRuns = 0;
        int violatingRuns = 0;
        for (int w : workers) {
            for (int i = 0; i < reps; i++) {
                final ProbeRun run;
                try {
                    run = proveInto(w + "w#" + i, keyFile, true, w);
                } catch (Throwable t) {
                    System.out.println("run " + w + "w#" + i + ": CRASHED " + rootCause(t));
                    violatingRuns++;
                    continue;
                }
                final boolean diverged = !DivergenceReport.compare(baseline, run).isEmpty();
                final boolean violated = !run.violations().isEmpty(); // hard: excludes warnings
                if (diverged || violated) {
                    if (diverged) {
                        divergedRuns++;
                    }
                    if (violated) {
                        violatingRuns++;
                    }
                    System.out.println(DivergenceReport.render(baseline, run));
                    if (divergedRuns + violatingRuns >= 5) {
                        System.out.println("(stopping after 5 divergent/violating runs)");
                        summary(divergedRuns, violatingRuns);
                        return;
                    }
                }
            }
        }
        summary(divergedRuns, violatingRuns);
    }

    private static void summary(int diverged, int violating) {
        System.out.println("SUMMARY: " + diverged + " runs diverged from the single-core proof, "
            + violating + " runs tripped a determinism check "
            + "(0 / 0 = no divergence observed in this run)");
    }

    /** Proves the file once and records its finished tree into a fresh {@link ProbeRun}. */
    private static ProbeRun proveInto(String label, Path keyFile, boolean parallel, int workers)
            throws Exception {
        final String prevParallel = System.getProperty(ParallelProver.PARALLEL_PROPERTY);
        final String prevThreads = System.getProperty(ParallelProver.THREADS_PROPERTY);
        if (parallel) {
            System.setProperty(ParallelProver.PARALLEL_PROPERTY, "true");
            System.setProperty(ParallelProver.THREADS_PROPERTY, Integer.toString(workers));
        } else {
            System.clearProperty(ParallelProver.PARALLEL_PROPERTY);
        }
        KeYEnvironment<?> env = null;
        final ProbeRun run = ProbeSink.startRun(label);
        try {
            env = KeYEnvironment.load(keyFile);
            final Proof proof = env.getLoadedProof();
            final ProofStarter starter = new ProofStarter(false);
            starter.init(proof);
            starter.start();
            recordProofTree(proof.root());
            return run;
        } finally {
            ProbeSink.endRun();
            if (env != null) {
                env.dispose();
            }
            restore(ParallelProver.PARALLEL_PROPERTY, prevParallel);
            restore(ParallelProver.THREADS_PROPERTY, prevThreads);
        }
    }

    /** Emits one proof-tree observation per node, keyed by its canonical path. */
    private static void recordProofTree(Node root) {
        emit(root, "");
    }

    /** Emits each node keyed by its canonical path (children visited sorted by subtree digest). */
    private static void emit(Node node, String path) {
        ProbeSink.observe(PROOF_TREE, path, labelOf(node));

        final int childCount = node.childrenCount();
        final String[] digest = new String[childCount];
        final Integer[] order = new Integer[childCount];
        for (int i = 0; i < childCount; i++) {
            digest[i] = subtreeDigest(node.child(i));
            order[i] = i;
        }
        java.util.Arrays.sort(order, (x, y) -> digest[x].compareTo(digest[y]));
        for (int rank = 0; rank < childCount; rank++) {
            emit(node.child(order[rank]), path + "." + rank);
        }
    }

    /** Canonical (sibling-order-independent) digest of a subtree; used only to order siblings. */
    private static String subtreeDigest(Node node) {
        final int childCount = node.childrenCount();
        final String[] childDigests = new String[childCount];
        for (int i = 0; i < childCount; i++) {
            childDigests[i] = subtreeDigest(node.child(i));
        }
        java.util.Arrays.sort(childDigests);
        final StringBuilder canonical = new StringBuilder(labelOf(node)).append('(');
        for (String d : childDigests) {
            canonical.append(d).append(',');
        }
        canonical.append(')');
        return sha256(canonical.toString());
    }

    private static String labelOf(Node node) {
        final RuleApp app = node.getAppliedRuleApp();
        if (app == null) {
            return node.isClosed() ? "<closed>" : "<open>";
        }
        return app.rule().name().toString();
    }

    private static String rootCause(Throwable t) {
        Throwable c = t;
        while (c.getCause() != null) {
            c = c.getCause();
        }
        final StackTraceElement[] st = c.getStackTrace();
        return c.getClass().getName() + (st.length > 0 ? " @ " + st[0] : "");
    }

    private static int[] parseInts(String csv) {
        final String[] parts = csv.split(",");
        final int[] out = new int[parts.length];
        for (int i = 0; i < parts.length; i++) {
            out[i] = Integer.parseInt(parts[i].trim());
        }
        return out;
    }

    private static void restore(String key, String value) {
        if (value == null) {
            System.clearProperty(key);
        } else {
            System.setProperty(key, value);
        }
    }

    private static String sha256(String s) {
        try {
            final MessageDigest md = MessageDigest.getInstance("SHA-256");
            final byte[] d = md.digest(s.getBytes(java.nio.charset.StandardCharsets.UTF_8));
            final StringBuilder sb = new StringBuilder(64);
            for (byte b : d) {
                sb.append(Character.forDigit((b >> 4) & 0xF, 16));
                sb.append(Character.forDigit(b & 0xF, 16));
            }
            return sb.toString();
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    private DivergenceDriver() {
    }
}
