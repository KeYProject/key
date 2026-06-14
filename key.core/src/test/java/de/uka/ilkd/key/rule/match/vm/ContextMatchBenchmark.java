/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.HelperClassForTests;
import de.uka.ilkd.key.util.ProofStarter;

import org.key_project.logic.op.Modality;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.vm.MatchProgram;
import org.key_project.prover.rules.matcher.vm.VMProgramInterpreter;
import org.key_project.prover.sequent.SequentFormula;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Isolated micro-benchmark for the program (symbolic-execution) find matcher: it compares the
 * cursor-based interpreter ({@link VMProgramInterpreter}) against the cursor-free compiled matcher
 * ({@link CompiledMatchProgram}), over the subset of program-bearing taclets that the compiler
 * handles (modality / context-block patterns; step 3). Both are built from the same find term and
 * run directly (no taclet index, strategy or proof pipeline), so this measures only the matcher.
 *
 * <p>
 * The corpus is harvested by running a bounded amount of symbolic execution on a real proof and
 * collecting the <em>modality</em> sub-terms (the redex candidates that drive program matching). By
 * default it runs on {@code proofStarter/CC/project.key}; point it at any problem with
 * {@code -Dbench.problems=/abs/a.key,/abs/b.key} (e.g. a straight-line problem), bound the harvest
 * with {@code -Dbench.steps=N} and the timed passes with {@code -Dbench.passes=N}. Run with
 * {@code ./gradlew :key.core:test --tests *ContextMatchBenchmark}.
 */
public class ContextMatchBenchmark {

    private static final MatchResultInfo EMPTY = MatchConditions.EMPTY_MATCHCONDITIONS;

    private static final int STEPS = Integer.getInteger("bench.steps", 6000);
    private static final int PASSES = Integer.getInteger("bench.passes", 30);

    private record Task(List<MatchProgram> interp, List<MatchProgram> compiled,
            List<JTerm> corpus, Services services, String label, int programTaclets,
            int[] deepProg, int[] deepTerm) {
    }

    @Test
    public void benchmarkInterpreterVsCompiled() throws Exception {
        final List<KeYEnvironment<DefaultUserInterfaceControl>> envs = new ArrayList<>();
        final List<Task> tasks = new ArrayList<>();
        try {
            for (String p : problemPaths()) {
                final Path path = Path.of(p.trim());
                if (!Files.exists(path)) {
                    System.out.println("  (skip, not found) " + path);
                    continue;
                }
                final KeYEnvironment<DefaultUserInterfaceControl> env =
                    KeYEnvironment.load(path, null, null, null);
                envs.add(env);
                tasks.add(buildTask(env, path.getFileName().toString()));
            }
            if (tasks.isEmpty()) {
                return;
            }

            // warmup
            for (int pass = 0; pass < 5; pass++) {
                for (Task t : tasks) {
                    run(t.interp, t);
                    run(t.compiled, t);
                    runDeep(t.interp, t);
                    runDeep(t.compiled, t);
                }
            }

            // (A) mixed sweep: every compilable taclet x every modality term (mostly fail-fast,
            // the common case in real proving); (B) focused on the deep/matching pairs.
            long interpMatches = 0, compMatches = 0, interpNanos = 0, compNanos = 0;
            long interpDeepNanos = 0, compDeepNanos = 0;
            for (int pass = 0; pass < PASSES; pass++) {
                for (Task t : tasks) {
                    long t0 = System.nanoTime();
                    interpMatches += run(t.interp, t);
                    interpNanos += System.nanoTime() - t0;

                    t0 = System.nanoTime();
                    compMatches += run(t.compiled, t);
                    compNanos += System.nanoTime() - t0;

                    t0 = System.nanoTime();
                    runDeep(t.interp, t);
                    interpDeepNanos += System.nanoTime() - t0;

                    t0 = System.nanoTime();
                    runDeep(t.compiled, t);
                    compDeepNanos += System.nanoTime() - t0;
                }
            }

            int deepPairs = 0;
            for (Task t : tasks) {
                deepPairs += t.deepProg.length;
                System.out.printf(
                    "  %-26s programTaclets=%d compilable=%d modalityCorpus=%d deepPairs=%d%n",
                    t.label, t.programTaclets, t.interp.size(), t.corpus.size(), t.deepProg.length);
            }
            System.out.printf(
                "[program matcher, %d task(s), %d passes]%n"
                    + "  (A) mixed sweep   interpreter=%.1f ms  compiled=%.1f ms  speedup=%.2fx%n"
                    + "  (B) deep matches  interpreter=%.1f ms  compiled=%.1f ms  speedup=%.2fx"
                    + "  (%d pairs/pass)%n",
                tasks.size(), PASSES,
                interpNanos / 1e6, compNanos / 1e6, (double) interpNanos / compNanos,
                interpDeepNanos / 1e6, compDeepNanos / 1e6,
                (double) interpDeepNanos / compDeepNanos, deepPairs);
            assertEquals(interpMatches, compMatches,
                "interpreter and compiled matcher must agree on the number of matches");
        } finally {
            for (KeYEnvironment<DefaultUserInterfaceControl> env : envs) {
                env.dispose();
            }
        }
    }

    private static Task buildTask(KeYEnvironment<DefaultUserInterfaceControl> env, String label) {
        final Proof proof = env.getLoadedProof();
        final Services services = proof.getServices();

        final ProofStarter ps = new ProofStarter(false);
        ps.init(proof);
        ps.setMaxRuleApplications(STEPS);
        ps.start();

        final List<JTerm> corpus = harvestModalityCorpus(proof);

        final List<MatchProgram> interp = new ArrayList<>();
        final List<MatchProgram> compiled = new ArrayList<>();
        int programTaclets = 0;
        for (Taclet t : proof.getInitConfig().activatedTaclets()) {
            if (!(t instanceof FindTaclet ft) || !(ft.find() instanceof JTerm find)
                    || !containsModality(find)) {
                continue;
            }
            programTaclets++;
            final CompiledMatchProgram comp = CompiledMatchProgram.compile(find);
            if (comp == null) {
                continue; // not compilable -> would use the interpreter in production
            }
            // oracle interpreter for the same find (programInstructions=false: monolithic
            // MatchProgramInstruction, the current production interpreter path)
            interp.add(
                new VMProgramInterpreter(
                    SyntaxElementMatchProgramGenerator.createProgram(find, false)));
            compiled.add(comp);
        }

        // collect the (program, term) pairs that actually match -- the deep matches that exercise
        // the program/context walk (the mixed sweep is >99% fail-fast and hides them)
        final List<int[]> deep = new ArrayList<>();
        for (int p = 0, np = interp.size(); p < np; p++) {
            for (int i = 0, n = corpus.size(); i < n; i++) {
                if (interp.get(p).match(corpus.get(i), EMPTY, services) != null) {
                    deep.add(new int[] { p, i });
                }
            }
        }
        final int[] deepProg = new int[deep.size()];
        final int[] deepTerm = new int[deep.size()];
        for (int k = 0; k < deep.size(); k++) {
            deepProg[k] = deep.get(k)[0];
            deepTerm[k] = deep.get(k)[1];
        }
        return new Task(interp, compiled, corpus, services, label, programTaclets, deepProg,
            deepTerm);
    }

    private static long run(List<MatchProgram> progs, Task t) {
        long matches = 0;
        for (int p = 0, np = progs.size(); p < np; p++) {
            final MatchProgram prog = progs.get(p);
            for (int i = 0, n = t.corpus.size(); i < n; i++) {
                if (prog.match(t.corpus.get(i), EMPTY, t.services) != null) {
                    matches++;
                }
            }
        }
        return matches;
    }

    /** runs only the (program, term) pairs that match -- isolates the deep program/context walk. */
    private static long runDeep(List<MatchProgram> progs, Task t) {
        long matches = 0;
        for (int k = 0, n = t.deepProg.length; k < n; k++) {
            if (progs.get(t.deepProg[k]).match(t.corpus.get(t.deepTerm[k]), EMPTY,
                t.services) != null) {
                matches++;
            }
        }
        return matches;
    }

    private static List<String> problemPaths() {
        final String prop = System.getProperty("bench.problems");
        if (prop != null && !prop.isBlank()) {
            return List.of(prop.split(","));
        }
        return List.of(HelperClassForTests.TESTCASE_DIRECTORY
                .resolve("proofStarter/CC/project.key").toString());
    }

    /** harvests the deduplicated modality sub-terms (redex candidates) from every proof node. */
    private static List<JTerm> harvestModalityCorpus(Proof proof) {
        final Set<JTerm> seen = new LinkedHashSet<>();
        final Iterator<Node> nodes = proof.root().subtreeIterator();
        while (nodes.hasNext()) {
            final Node n = nodes.next();
            for (SequentFormula sf : n.sequent()) {
                collectModalities((JTerm) sf.formula(), seen);
            }
        }
        return new ArrayList<>(seen);
    }

    private static void collectModalities(JTerm t, Set<JTerm> out) {
        if (t.op() instanceof Modality) {
            out.add(t);
        }
        for (int i = 0, n = t.arity(); i < n; i++) {
            collectModalities(t.sub(i), out);
        }
    }

    private static boolean containsModality(JTerm t) {
        if (t.op() instanceof Modality) {
            return true;
        }
        for (int i = 0, n = t.arity(); i < n; i++) {
            if (containsModality(t.sub(i))) {
                return true;
            }
        }
        return false;
    }
}
