/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.mt;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.impl.ParallelProver;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.ProofStarter;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIfSystemProperty;

/**
 * Synthetic speedup/scaling benchmark for the goal-level parallel prover, complementing the
 * real-proof {@link MtSpeedupBenchmark}. It generates self-contained Java-DL {@code .key} problems
 * whose proof-tree <em>shape</em> is controlled, to map out the best/worst case of goal-level
 * parallelism. Enable with {@code -Dkey.mt.benchmark=true} (skipped otherwise). It asserts nothing,
 * only measures and prints.
 *
 * <p>
 * The governing intuition: the wall-clock of a goal-parallel run is bounded below by the
 * <em>critical path</em> (the most expensive single branch), so speedup tracks how the work is
 * distributed over independent branches.
 * <ul>
 * <li><b>split_ifs</b> — N independent {@code if}s on symbolic booleans, so symbolic execution fans
 * out into 2^N balanced, cheap leaves. Best case for parallelism (lots of short independent
 * branches), but split/commit overhead per node is exposed because the leaves are tiny.
 * <li><b>split_work</b> — the same 2^N fan-out, but each leaf then runs a block of straight-line
 * work, so there is substantial <em>independent</em> work per branch. This is the configuration
 * where parallelism should pay off most (work dominates the serial split overhead).
 * <li><b>linear_assign</b> — one long straight-line block: a single branch, no splitting. Worst
 * case: the critical path is the whole proof, so no speedup is possible (the ceiling is ~1x; this
 * isolates the overhead the parallel machinery adds on a non-parallel proof).
 * <li><b>while_unroll</b> — a bounded loop unrolled (LOOP_EXPAND): an almost-linear chain with a
 * tiny exit branch per iteration. Realistic worst case (a loop without an invariant).
 * </ul>
 *
 * <p>
 * Sizes come from system properties (so the shape can be swept without recompiling):
 * {@code -Dkey.mt.synth.splits} (default 11), {@code -Dkey.mt.synth.work} (default 250),
 * {@code -Dkey.mt.synth.linear} (default 2500), {@code -Dkey.mt.synth.loop} (default 1200). Worker
 * counts from {@code -Dkey.mt.benchmark.threads} (default {@code 1,2,4,8}).
 *
 * @author Claude (KeY multithreading effort)
 */
@EnabledIfSystemProperty(named = "key.mt.benchmark", matches = "true")
public class MtSyntheticBenchmark {

    private static final int MAX_STEPS = 2_000_000;

    private record Case(String name, String content, boolean loopExpand) {
    }

    @Test
    void benchmark() throws Exception {
        // split_work fans out less than split_ifs (2^worksplits branches, each with real work) so
        // the total node count stays in the same ballpark as a large real proof (~tens of
        // thousands), within the test heap. split_ifs keeps the wide-but-shallow fan-out.
        final int splits = intProp("key.mt.synth.splits", 11);
        final int worksplits = intProp("key.mt.synth.worksplits", 7);
        final int work = intProp("key.mt.synth.work", 120);
        final int linear = intProp("key.mt.synth.linear", 800);
        final int loop = intProp("key.mt.synth.loop", 400);

        List<Case> cases = List.of(
            new Case("split_ifs(" + splits + ")", splitIfs(splits), false),
            new Case("split_work(" + worksplits + "x" + work + ")", splitWork(worksplits, work),
                false),
            new Case("linear_assign(" + linear + ")", linearAssign(linear), false),
            new Case("while_unroll(" + loop + ")", whileUnroll(loop), true));

        int cores = Runtime.getRuntime().availableProcessors();
        List<Integer> workerCounts = workerCounts(cores);

        System.out.printf("%n[mt-synthetic] cores=%d worker-counts=%s%n", cores, workerCounts);
        System.out.printf("%-26s %10s %8s %7s %8s %7s %6s%n", "case", "config", "time(ms)",
            "speedup", "nodes", "leaves", "depth");

        for (Case c : cases) {
            Path keyFile = Files.createTempFile("mt-synth-", ".key");
            Files.writeString(keyFile, c.content);
            try {
                // Warm up BOTH the single-threaded and the parallel code paths (JIT) before timing.
                // Otherwise the first parallel configuration pays for cold compilation of the whole
                // parallel machinery and reads as a spurious slowdown.
                int warmWorkers = workerCounts.get(workerCounts.size() - 1);
                run(keyFile, 0, c.loopExpand);
                if (warmWorkers > 0) {
                    run(keyFile, warmWorkers, c.loopExpand);
                }
                Run base = best(keyFile, 0, c.loopExpand);
                System.out.printf("%-26s %10s %8d %7s %8d %7d %6d%n", c.name, "single", base.millis,
                    "1.00x", base.nodes, base.leaves, base.depth);
                for (int w : workerCounts) {
                    Run r = best(keyFile, w, c.loopExpand);
                    double speedup = r.millis > 0 ? (double) base.millis / r.millis : 0.0;
                    System.out.printf("%-26s %10s %8d %6.2fx %8d %7d %6d%n", "", w + "-worker",
                        r.millis, speedup, r.nodes, r.leaves, r.depth);
                }
            } catch (Throwable t) {
                // Keep going with the remaining cases: a too-large case (e.g. OOM) should not abort
                // the whole table.
                System.out.printf("%-26s  FAILED: %s%n", c.name, t);
            } finally {
                Files.deleteIfExists(keyFile);
            }
        }
    }

    /** Best (fastest) of two timed runs — reduces the effect of GC/scheduling noise. */
    private static Run best(Path keyFile, int workers, boolean loopExpand) throws Exception {
        Run a = run(keyFile, workers, loopExpand);
        Run b = run(keyFile, workers, loopExpand);
        return a.millis <= b.millis ? a : b;
    }

    /** Runs one generated proof; {@code workers == 0} means the single-threaded baseline. */
    private static Run run(Path keyFile, int workers, boolean loopExpand) throws Exception {
        KeYEnvironment<?> env = KeYEnvironment.load(keyFile);
        String prevEnabled = System.getProperty(ParallelProver.PARALLEL_PROPERTY);
        String prevThreads = System.getProperty(ParallelProver.THREADS_PROPERTY);
        if (workers > 0) {
            System.setProperty(ParallelProver.PARALLEL_PROPERTY, "true");
            System.setProperty(ParallelProver.THREADS_PROPERTY, Integer.toString(workers));
        } else {
            System.clearProperty(ParallelProver.PARALLEL_PROPERTY);
        }
        try {
            Proof proof = env.getLoadedProof();
            ProofStarter starter = new ProofStarter(false);
            starter.init(proof);
            starter.setMaxRuleApplications(MAX_STEPS);
            if (loopExpand) {
                StrategyProperties sp =
                    proof.getSettings().getStrategySettings().getActiveStrategyProperties();
                sp.setProperty(StrategyProperties.LOOP_OPTIONS_KEY, StrategyProperties.LOOP_EXPAND);
                starter.setStrategyProperties(sp);
            }
            long t0 = System.nanoTime();
            starter.start();
            long millis = (System.nanoTime() - t0) / 1_000_000L;
            return new Run(millis, proof.closed(), proof.countNodes(), countLeaves(proof),
                maxDepth(proof));
        } finally {
            restore(ParallelProver.PARALLEL_PROPERTY, prevEnabled);
            restore(ParallelProver.THREADS_PROPERTY, prevThreads);
            env.dispose();
        }
    }

    // ---- problem generators -------------------------------------------------

    /** N independent ifs on symbolic booleans -> 2^N balanced, cheap leaves. */
    private static String splitIfs(int n) {
        StringBuilder vars = new StringBuilder("int x;");
        StringBuilder prog = new StringBuilder();
        for (int i = 0; i < n; i++) {
            vars.append(" boolean b").append(i).append(";");
            prog.append("if (b").append(i).append(") { x = x + 1; } else { x = x - 1; }\n");
        }
        return problem(vars.toString(), prog.toString(), "true");
    }

    /** 2^N fan-out, then a straight-line block of work executed in every leaf. */
    private static String splitWork(int n, int work) {
        StringBuilder vars = new StringBuilder("int x;");
        StringBuilder prog = new StringBuilder();
        for (int i = 0; i < n; i++) {
            vars.append(" boolean b").append(i).append(";");
            prog.append("if (b").append(i).append(") { x = x + 1; } else { x = x - 1; }\n");
        }
        for (int j = 0; j < work; j++) {
            prog.append("x = x + 1;\n");
        }
        return problem(vars.toString(), prog.toString(), "true");
    }

    /** One long straight-line block: a single branch, no splitting (speedup ceiling ~1x). */
    private static String linearAssign(int n) {
        StringBuilder prog = new StringBuilder("x = 0;\n");
        for (int i = 0; i < n; i++) {
            prog.append("x = x + 1;\n");
        }
        return problem("int x;", prog.toString(), "true");
    }

    /** A bounded loop, unrolled (LOOP_EXPAND): almost-linear with a tiny exit branch per step. */
    private static String whileUnroll(int bound) {
        String prog = "i = 0; x = 0;\nwhile (i < " + bound + ") { x = x + i; i = i + 1; }\n";
        return problem("int x; int i;", prog, "true");
    }

    private static String problem(String vars, String prog, String post) {
        return "\\programVariables {\n  " + vars + "\n}\n\n"
            + "\\problem {\n  \\<{\n" + prog + "  }\\> " + post + "\n}\n";
    }

    // ---- proof-tree shape ---------------------------------------------------

    private static int countLeaves(Proof proof) {
        int leaves = 0;
        Deque<Node> stack = new ArrayDeque<>();
        stack.push(proof.root());
        while (!stack.isEmpty()) {
            Node n = stack.pop();
            int kids = n.childrenCount();
            if (kids == 0) {
                leaves++;
            } else {
                for (int i = 0; i < kids; i++) {
                    stack.push(n.child(i));
                }
            }
        }
        return leaves;
    }

    private static int maxDepth(Proof proof) {
        int max = 0;
        Deque<Node> nodes = new ArrayDeque<>();
        Deque<Integer> depths = new ArrayDeque<>();
        nodes.push(proof.root());
        depths.push(1);
        while (!nodes.isEmpty()) {
            Node n = nodes.pop();
            int d = depths.pop();
            max = Math.max(max, d);
            for (int i = 0; i < n.childrenCount(); i++) {
                nodes.push(n.child(i));
                depths.push(d + 1);
            }
        }
        return max;
    }

    // ---- plumbing -----------------------------------------------------------

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

    private static int intProp(String key, int dflt) {
        String v = System.getProperty(key);
        return v == null || v.isBlank() ? dflt : Integer.parseInt(v.trim());
    }

    private static void restore(String key, String previous) {
        if (previous == null) {
            System.clearProperty(key);
        } else {
            System.setProperty(key, previous);
        }
    }

    private record Run(long millis, boolean closed, int nodes, int leaves, int depth) {
    }
}
