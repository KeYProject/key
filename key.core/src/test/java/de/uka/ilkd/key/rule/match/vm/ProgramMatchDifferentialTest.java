/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm;

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
import de.uka.ilkd.key.rule.match.vm.instructions.MatchContextStatementBlockInstruction;
import de.uka.ilkd.key.rule.match.vm.instructions.MatchSubProgramInstruction;
import de.uka.ilkd.key.util.HelperClassForTests;
import de.uka.ilkd.key.util.ProofStarter;

import org.key_project.logic.op.Modality;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.vm.VMProgramInterpreter;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;
import org.key_project.prover.sequent.SequentFormula;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Differential test / oracle for the matcher work. For every find-taclet of the full Java taclet
 * base it builds, in the same JVM, the interpreter <em>oracle</em>
 * ({@code key.matcher.programInstructions=false}, modality programs matched by the monolithic
 * {@code MatchProgramInstruction} delegating to {@code ProgramElement.match}) and, where
 * applicable,
 * the <em>converted</em> interpreter ({@code =true}: generic programs via
 * {@link MatchSubProgramInstruction}, context blocks via
 * {@link MatchContextStatementBlockInstruction}) and the cursor-free <em>compiled</em> matcher
 * ({@link CompiledMatchProgram}, incl. modality / context-block / bound-variable patterns). All are
 * run over a corpus of terms harvested from a real proof and asserted to produce identical results
 * (match success/failure and the resulting instantiations, including the context-block
 * prefix/suffix
 * instantiation).
 *
 * <p>
 * This guards the converted and compiled matchers against the interpreter at the unit-test level.
 * The complementary end-to-end check is identical proof statistics (nodes / branches / rule
 * applications) for a full {@code --auto} proof with the flag on vs off (the CLI
 * {@code .auto.proof}
 * stores only the problem, not the proof tree, so a file diff is not a valid replay check).
 */
public class ProgramMatchDifferentialTest {

    private static final MatchResultInfo EMPTY = MatchConditions.EMPTY_MATCHCONDITIONS;

    /** the symbolic-execution proof whose terms form the matching corpus. */
    private static final Path CORPUS_PROOF =
        HelperClassForTests.TESTCASE_DIRECTORY.resolve("proofStarter/CC/project.key");

    /** cap on symbolic-execution steps run to harvest the corpus (keeps the test fast). */
    private static final int CORPUS_STEPS = 6000;

    @Test
    public void convertedMatchesInterpreter() throws Exception {
        final KeYEnvironment<DefaultUserInterfaceControl> env =
            KeYEnvironment.load(CORPUS_PROOF, null, null, null);
        try {
            final Proof proof = env.getLoadedProof();
            final Services services = proof.getServices();

            // run a bounded amount of symbolic execution to populate the proof tree with terms at
            // many execution stages (method frames, peeled blocks, loops, ...)
            final ProofStarter ps = new ProofStarter(false);
            ps.init(proof);
            ps.setMaxRuleApplications(CORPUS_STEPS);
            ps.start();

            final List<JTerm> corpus = harvestCorpus(proof);

            int findTaclets = 0;
            int programTaclets = 0;
            int convertedContext = 0;
            int convertedGeneric = 0;
            int compiledTaclets = 0;
            int compiledBoundVar = 0;
            long matches = 0;
            int comparisons = 0;
            for (Taclet t : proof.getInitConfig().activatedTaclets()) {
                if (!(t instanceof FindTaclet ft) || !(ft.find() instanceof JTerm find)) {
                    continue;
                }
                findTaclets++;
                final boolean program = containsModality(find);
                final VMProgramInterpreter oracle = new VMProgramInterpreter(
                    SyntaxElementMatchProgramGenerator.createProgram(find, false));
                // the cursor-free compiled matcher; null if not (yet) compilable
                final CompiledMatchProgram compiled = CompiledMatchProgram.compile(find);
                if (compiled != null) {
                    compiledTaclets++;
                    if (containsBoundVars(find)) {
                        compiledBoundVar++;
                    }
                }
                // the converted interpreter (programInstructions=true) only differs for programs
                VMProgramInterpreter converted = null;
                if (program) {
                    programTaclets++;
                    final VMInstruction[] convertedProg =
                        SyntaxElementMatchProgramGenerator.createProgram(find, true);
                    if (contains(convertedProg, MatchContextStatementBlockInstruction.class)) {
                        convertedContext++;
                    }
                    if (contains(convertedProg, MatchSubProgramInstruction.class)) {
                        convertedGeneric++;
                    }
                    converted = new VMProgramInterpreter(convertedProg);
                }

                for (JTerm term : corpus) {
                    final MatchResultInfo oracleRes = oracle.match(term, EMPTY, services);
                    comparisons++;
                    if (converted != null) {
                        assertSameResult(t, term, oracleRes,
                            converted.match(term, EMPTY, services));
                    }
                    if (compiled != null) {
                        assertSameResult(t, term, oracleRes, compiled.match(term, EMPTY, services));
                    }
                    if (oracleRes != null) {
                        matches++;
                    }
                }
            }

            System.out.printf(
                "[program-match differential] findTaclets=%d programTaclets=%d convertedContext=%d "
                    + "convertedGeneric=%d compiled=%d (boundVar=%d) corpus=%d comparisons=%d "
                    + "matches=%d%n",
                findTaclets, programTaclets, convertedContext, convertedGeneric, compiledTaclets,
                compiledBoundVar, corpus.size(), comparisons, matches);
            // sanity floor: the run must actually exercise the step-2 context-block conversion
            assertEquals(true, convertedContext > 0,
                "expected at least some taclets to use the converted context-block matcher");
            // sanity floor: the run must actually exercise the compiled program matcher (step 3)
            assertEquals(true, compiledTaclets > 0,
                "expected at least some program taclets to compile");
            // sanity floor: the run must actually exercise compiled bound-variable matching
            assertEquals(true, compiledBoundVar > 0,
                "expected at least some bound-variable taclets to compile");
        } finally {
            env.dispose();
        }
    }

    /** asserts that oracle and converted matcher agree (success/failure and instantiations). */
    private static void assertSameResult(Taclet t, JTerm term, MatchResultInfo oracle,
            MatchResultInfo converted) {
        final boolean oracleOk = oracle != null;
        final boolean convertedOk = converted != null;
        assertEquals(oracleOk, convertedOk,
            () -> "match success differs for taclet " + t.name() + " on " + term);
        if (oracleOk) {
            final var oracleInst = ((MatchConditions) oracle).getInstantiations();
            final var convertedInst = ((MatchConditions) converted).getInstantiations();
            assertEquals(oracleInst, convertedInst,
                () -> "instantiations differ for taclet " + t.name() + " on " + term
                    + "\n  oracle:    " + oracleInst
                    + "\n  converted: " + convertedInst);
            // the context instantiation (prefix/suffix positions) is the critical step-2 output
            assertEquals(
                String.valueOf(oracleInst.getContextInstantiation()),
                String.valueOf(convertedInst.getContextInstantiation()),
                () -> "context instantiation differs for taclet " + t.name() + " on " + term);
        }
    }

    /** collects a deduplicated corpus of subterms from every node of the proof tree. */
    private static List<JTerm> harvestCorpus(Proof proof) {
        final Set<JTerm> seen = new LinkedHashSet<>();
        final Iterator<Node> nodes = proof.root().subtreeIterator();
        while (nodes.hasNext()) {
            final Node n = nodes.next();
            for (SequentFormula sf : n.sequent()) {
                collectSubterms((JTerm) sf.formula(), seen);
            }
        }
        return new ArrayList<>(seen);
    }

    private static void collectSubterms(JTerm t, Set<JTerm> out) {
        out.add(t);
        for (int i = 0, n = t.arity(); i < n; i++) {
            collectSubterms(t.sub(i), out);
        }
    }

    /** whether the term tree binds any variable (quantifier, substitution, ...). */
    private static boolean containsBoundVars(JTerm t) {
        if (!t.boundVars().isEmpty()) {
            return true;
        }
        for (int i = 0, n = t.arity(); i < n; i++) {
            if (containsBoundVars(t.sub(i))) {
                return true;
            }
        }
        return false;
    }

    /** whether the term tree contains a modality (i.e. carries a Java program). */
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

    /** whether the generated (top-level) program contains an instruction of the given kind. */
    private static boolean contains(VMInstruction[] program, Class<? extends VMInstruction> kind) {
        for (VMInstruction instr : program) {
            if (kind.isInstance(instr)) {
                return true;
            }
        }
        return false;
    }
}
