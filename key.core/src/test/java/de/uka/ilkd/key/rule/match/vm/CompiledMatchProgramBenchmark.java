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
import org.key_project.prover.rules.matcher.vm.MatchProgram;
import org.key_project.prover.rules.matcher.vm.VMProgramInterpreter;
import org.key_project.prover.sequent.SequentFormula;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Isolated micro-benchmark for the find matcher (no taclet index, strategy or proof pipeline), over
 * the subset of the real taclet base that the compiler handles. It serves two purposes:
 *
 * <ol>
 * <li>the headline comparison {@link VMProgramInterpreter} vs {@link CompiledMatchProgram} (the
 * cursor-free win), and</li>
 * <li>the <em>no-overhead</em> check for the match-plan framework: the matchers built through
 * {@link JavaMatchPlanBuilder} (one description, two back-ends) are timed alongside the
 * hand-written
 * ones. Since the plan is lowered once at construction to the same {@code VMInstruction[]} /
 * cursor-free closures, the framework-built matchers must run at parity with the hand-written ones
 * (the IR adds no per-match cost).</li>
 * </ol>
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

    /**
     * the four matchers built per compilable find-taclet: hand-written and framework, each
     * back-end.
     */
    private record Task(List<VMProgramInterpreter> handInterps, List<MatchProgram> handComps,
            List<VMProgramInterpreter> planInterps, List<MatchProgram> planComps,
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
                run(t.handInterps, t);
                run(t.handComps, t);
                run(t.planInterps, t);
                run(t.planComps, t);
            }
        }

        // timed: alternate phases per pass to average out JIT / cache effects
        final int passes = 30;
        long handInterpN = 0, handCompN = 0, planInterpN = 0, planCompN = 0;
        long handInterpM = 0, handCompM = 0, planInterpM = 0, planCompM = 0;
        for (int pass = 0; pass < passes; pass++) {
            for (Task t : tasks) {
                long t0 = System.nanoTime();
                handInterpM += run(t.handInterps, t);
                handInterpN += System.nanoTime() - t0;

                t0 = System.nanoTime();
                planInterpM += run(t.planInterps, t);
                planInterpN += System.nanoTime() - t0;

                t0 = System.nanoTime();
                handCompM += run(t.handComps, t);
                handCompN += System.nanoTime() - t0;

                t0 = System.nanoTime();
                planCompM += run(t.planComps, t);
                planCompN += System.nanoTime() - t0;
            }
        }

        System.out.printf("[isolated matcher, %d problem(s)]%n", tasks.size());
        System.out.printf(
            "  interpreter : hand-written=%.1f ms  framework=%.1f ms  (overhead %+.1f%%)%n",
            handInterpN / 1e6, planInterpN / 1e6,
            100.0 * (planInterpN - handInterpN) / handInterpN);
        System.out.printf(
            "  compiled    : hand-written=%.1f ms  framework=%.1f ms  (overhead %+.1f%%)%n",
            handCompN / 1e6, planCompN / 1e6, 100.0 * (planCompN - handCompN) / handCompN);
        System.out.printf("  speedup (framework compiled vs framework interpreter) = %.2fx%n",
            (double) planInterpN / planCompN);
        // all four matchers must see exactly the same matches
        assertEquals(handInterpM, handCompM, "hand-written back-ends must agree on #matches");
        assertEquals(handInterpM, planInterpM,
            "framework interpreter must agree with hand-written");
        assertEquals(handInterpM, planCompM, "framework compiled must agree with hand-written");
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

        final List<VMProgramInterpreter> handInterps = new ArrayList<>();
        final List<MatchProgram> handComps = new ArrayList<>();
        final List<VMProgramInterpreter> planInterps = new ArrayList<>();
        final List<MatchProgram> planComps = new ArrayList<>();
        int findTaclets = 0;
        for (Taclet t : pa.getFirstProof().getInitConfig().activatedTaclets()) {
            if (!(t instanceof FindTaclet ft)) {
                continue;
            }
            findTaclets++;
            final JTerm find = (JTerm) ft.find();
            final MatchProgram handComp = CompiledMatchProgram.compile(find);
            final MatchProgram planComp = JavaMatchPlanBuilder.compiledProgram(find);
            if (handComp == null || planComp == null) {
                continue; // restrict to the compilable subset, identical for both
            }
            handComps.add(handComp);
            planComps.add(planComp);
            handInterps.add(
                new VMProgramInterpreter(SyntaxElementMatchProgramGenerator.createProgram(find)));
            planInterps.add(
                new VMProgramInterpreter(JavaMatchPlanBuilder.interpreterProgram(find)));
        }
        System.out.printf("  %-22s findTaclets=%4d compilable=%4d (%2.0f%%) corpus=%d%n",
            path.getFileName(), findTaclets, handComps.size(),
            findTaclets == 0 ? 0 : 100.0 * handComps.size() / findTaclets, corpus.size());
        return new Task(handInterps, handComps, planInterps, planComps, corpus, services);
    }

    private static long run(List<? extends MatchProgram> programs, Task t) {
        long matches = 0;
        for (int p = 0, np = programs.size(); p < np; p++) {
            final MatchProgram prog = programs.get(p);
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
