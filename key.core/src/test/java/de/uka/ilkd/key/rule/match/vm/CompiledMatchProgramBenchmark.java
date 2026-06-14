/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.vm.VMProgramInterpreter;
import org.key_project.prover.sequent.SequentFormula;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Isolated micro-benchmark for the find matcher: it compares {@link VMProgramInterpreter} against
 * {@link CompiledMatchProgram} directly (no taclet index, strategy or proof pipeline), over the
 * subset of the real taclet base that the compiler handles (FOL / integer / propositional patterns;
 * program symbolic-execution rules are excluded by the compiler and thus not part of the
 * comparison).
 *
 * <p>
 * By default it runs on the self-contained {@code tacletMatch1.key}. Point it at a wider set (e.g.
 * the bundled TPTP PUZ/SYN problems, which load the full FOL taclet base) with
 * {@code -Dbench.problems=/abs/a.key,/abs/b.key}. Run with
 * {@code ./gradlew :key.core:test --tests *CompiledMatchProgramBenchmark}.
 */
public class CompiledMatchProgramBenchmark {

    private static final MatchResultInfo EMPTY = MatchConditions.EMPTY_MATCHCONDITIONS;

    /** supplementary closed formulas (used when a problem's own sequent yields few terms). */
    private static final String[] CORPUS_FORMULAS = {
        "A & B", "(!A | (A <-> B)) & B", "A -> (B -> A)", "\\forall int x; x >= 0",
        "\\forall int x; x + 1 > x", "\\forall int x; \\exists int y; x + y = 0",
        "1 + 2 * 3 = 7", "\\forall int x; \\forall int y; (x + y = y + x)"
    };

    private record Task(List<VMProgramInterpreter> interps, List<CompiledMatchProgram> comps,
            List<JTerm> corpus, Services services) {
    }

    @Test
    public void benchmarkInterpreterVsCompiled() {
        final List<Task> tasks = new ArrayList<>();
        for (String p : problemPaths()) {
            final Task t = buildTask(p);
            if (t != null) {
                tasks.add(t);
            }
        }
        if (tasks.isEmpty()) {
            return;
        }

        // warmup
        for (int pass = 0; pass < 5; pass++) {
            for (Task t : tasks) {
                runInterp(t);
                runComp(t);
            }
        }

        // timed: alternate phases per pass to average out JIT / cache effects
        final int passes = 30;
        long interpMatches = 0, compMatches = 0, interpNanos = 0, compNanos = 0;
        for (int pass = 0; pass < passes; pass++) {
            for (Task t : tasks) {
                long t0 = System.nanoTime();
                interpMatches += runInterp(t);
                interpNanos += System.nanoTime() - t0;

                t0 = System.nanoTime();
                compMatches += runComp(t);
                compNanos += System.nanoTime() - t0;
            }
        }

        System.out.printf("[isolated matcher, %d problem(s)] interpreter=%.1f ms  compiled=%.1f ms"
            + "  speedup=%.2fx  (matches interp=%d comp=%d)%n",
            tasks.size(), interpNanos / 1e6, compNanos / 1e6,
            (double) interpNanos / compNanos, interpMatches / passes, compMatches / passes);
        assertEquals(interpMatches, compMatches,
            "compiled and interpreter must agree on the number of matches");
    }

    private static List<String> problemPaths() {
        final String prop = System.getProperty("bench.problems");
        if (prop != null && !prop.isBlank()) {
            return List.of(prop.split(","));
        }
        return List.of(HelperClassForTests.TESTCASE_DIRECTORY.resolve("tacletmatch")
                .resolve("tacletMatch1.key").toString());
    }

    private static Task buildTask(String pathStr) {
        final Path path = Path.of(pathStr.trim());
        if (!Files.exists(path)) {
            System.out.println("  (skip, not found) " + path);
            return null;
        }
        final ProofAggregate pa = HelperClassForTests.parse(path);
        final Services services = pa.getFirstProof().getServices();

        final List<JTerm> corpus = new ArrayList<>();
        for (SequentFormula sf : pa.getFirstProof().root().sequent()) {
            collectSubterms((JTerm) sf.formula(), corpus);
        }
        for (String f : CORPUS_FORMULAS) {
            try {
                collectSubterms(services.getTermBuilder().parseTerm(f), corpus);
            } catch (Exception ignored) {
                // formula not parseable in this problem's signature
            }
        }

        final List<VMProgramInterpreter> interps = new ArrayList<>();
        final List<CompiledMatchProgram> comps = new ArrayList<>();
        int findTaclets = 0;
        for (Taclet t : pa.getFirstProof().getInitConfig().activatedTaclets()) {
            if (!(t instanceof FindTaclet ft)) {
                continue;
            }
            findTaclets++;
            final JTerm find = (JTerm) ft.find();
            final CompiledMatchProgram comp = CompiledMatchProgram.compile(find);
            if (comp == null) {
                continue;
            }
            comps.add(comp);
            interps.add(
                new VMProgramInterpreter(SyntaxElementMatchProgramGenerator.createProgram(find)));
        }
        System.out.printf("  %-22s findTaclets=%4d compilable=%4d (%2.0f%%) corpus=%d%n",
            path.getFileName(), findTaclets, comps.size(),
            findTaclets == 0 ? 0 : 100.0 * comps.size() / findTaclets, corpus.size());
        return new Task(interps, comps, corpus, services);
    }

    private static long runInterp(Task t) {
        long matches = 0;
        for (int p = 0, np = t.interps.size(); p < np; p++) {
            final VMProgramInterpreter prog = t.interps.get(p);
            for (int i = 0, n = t.corpus.size(); i < n; i++) {
                if (prog.match(t.corpus.get(i), EMPTY, t.services) != null) {
                    matches++;
                }
            }
        }
        return matches;
    }

    private static long runComp(Task t) {
        long matches = 0;
        for (int p = 0, np = t.comps.size(); p < np; p++) {
            final CompiledMatchProgram prog = t.comps.get(p);
            for (int i = 0, n = t.corpus.size(); i < n; i++) {
                if (prog.match(t.corpus.get(i), EMPTY, t.services) != null) {
                    matches++;
                }
            }
        }
        return matches;
    }

    private static void collectSubterms(JTerm t, List<JTerm> out) {
        out.add(t);
        for (int i = 0, n = t.arity(); i < n; i++) {
            collectSubterms(t.sub(i), out);
        }
    }
}
