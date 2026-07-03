/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.naming;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.prover.impl.ParallelProver;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.HelperClassForTests;
import de.uka.ilkd.key.util.ProofStarter;

import org.key_project.logic.Name;
import org.key_project.logic.PosInTerm;
import org.key_project.logic.op.Function;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Regression harness for the fresh-naming refactoring (#3851): pins the naming invariants that
 * must hold BEFORE and AFTER moving name generation from global counters to goal-local proof
 * state. The assertions are deliberately invariant-based (locality, prune-reset, origin
 * visibility, bounded length) rather than exact-name-based, so they gate every migration step
 * without needing to change alongside the naming scheme.
 */
public class TestNamingInvariants {

    private static final Path NAMING_DIR =
        HelperClassForTests.TESTCASE_DIRECTORY.resolve("naming");

    // ---------------------------------------------------------------- skolem branch locality

    /**
     * Sibling branches skolemizing bound variables with the same base name must produce the SAME
     * skolem name on both branches: names are branch-local and must not leak into (or be blocked
     * by) sibling branches. Pruning and redoing must reproduce the same names.
     */
    @Test
    public void skolemNamesAreBranchLocalAndPruneStable() throws Exception {
        final KeYEnvironment<?> env = load("skolemSiblings.key");
        try {
            final Proof proof = env.getLoadedProof();
            splitAndSkolemize(proof);

            final List<String> first = skolemNamesPerGoal(proof, "idx");
            assertEquals(2, first.size(), "expected two open branches");
            assertEquals(first.get(0), first.get(1),
                "sibling branches must reuse the same branch-local skolem name, got " + first);

            // origin visibility + length policy: the name must reveal the bound variable it
            // came from and stay short
            for (final String name : first) {
                assertTrue(name.contains("idx"),
                    "skolem name should reveal its origin 'idx': " + name);
                assertTrue(name.length() <= 10,
                    "skolem names should stay short (<=10 chars): " + name);
            }

            // prune to root and redo: names must be reproduced exactly (state-derived)
            proof.pruneProof(proof.root());
            splitAndSkolemize(proof);
            final List<String> second = skolemNamesPerGoal(proof, "idx");
            assertEquals(first, second,
                "pruning and redoing must reproduce identical skolem names");
        } finally {
            env.dispose();
        }
    }

    // ------------------------------------------------------------------- addrule (hide) channel

    /**
     * Hiding a formula introduces an {@code insert_hidden...} taclet via the {@code \addrules}
     * channel. The taclet must be goal-local (invisible to the sibling branch), its name must be
     * reproduced when the proof is pruned and the hide is redone (state-derived id), and pruning
     * must remove it from the goal's local rules.
     */
    @Test
    public void hiddenFormulaTacletIsGoalLocalAndPruneSafe() throws Exception {
        final KeYEnvironment<?> env = load("hideReinsert.key");
        try {
            final Proof proof = env.getLoadedProof();
            splitAndHide(proof);

            // exactly one open goal performed the hide; find it and its sibling
            Goal hideGoal = null;
            Goal siblingGoal = null;
            for (final Goal g : proof.openGoals()) {
                if (localRules(g).size() == 1) {
                    hideGoal = g;
                } else {
                    siblingGoal = g;
                }
            }
            assertNotNull(hideGoal, "one goal must carry the introduced insert_hidden taclet");
            assertNotNull(siblingGoal, "the sibling goal must exist");

            final String introducedName = localRules(hideGoal).get(0).taclet().name().toString();
            assertTrue(introducedName.startsWith("insert_hidden"),
                "introduced rule should be an insert_hidden taclet: " + introducedName);
            assertEquals(0, localRules(siblingGoal).size(),
                "the introduced taclet must not leak to the sibling branch");

            // prune the hide away: the goal-local rule must disappear
            proof.pruneProof(hideGoal.node().parent());
            for (final Goal g : proof.openGoals()) {
                for (final NoPosTacletApp app : g.node().getLocalIntroducedRules()) {
                    assertFalse(app.taclet().name().toString().equals(introducedName),
                        "pruned insert_hidden taclet must not survive in local rules");
                }
            }

            // redo the hide on the pruned-back goal (state-derived => same name expected)
            applyOnFormula(proof, proof.openGoals().head(), "hide_left", 1, true);
            Goal redoneGoal = null;
            for (final Goal g : proof.openGoals()) {
                if (localRules(g).size() == 1) {
                    redoneGoal = g;
                }
            }
            assertNotNull(redoneGoal);
            assertEquals(introducedName,
                localRules(redoneGoal).get(0).taclet().name().toString(),
                "redoing the hide after pruning must reproduce the same taclet name");
        } finally {
            env.dispose();
        }
    }

    // ------------------------------------------------------------------ addProgramVariable

    /**
     * {@code Goal.addProgramVariable} must register the variable in the goal-LOCAL namespace
     * only: invisible to sibling goals and to the proof-global namespace, and gone after pruning.
     */
    @Test
    public void addedProgramVariableIsGoalLocalAndPruneSafe() throws Exception {
        final KeYEnvironment<?> env = load("skolemSiblings.key");
        try {
            final Proof proof = env.getLoadedProof();
            applyOnFormula(proof, proof.openGoals().head(), "andRight", 1, false);
            assertEquals(2, proof.openGoals().size());

            final Goal goal = proof.openGoals().head();
            final Goal sibling = proof.openGoals().tail().head();
            final Services services = proof.getServices();

            final Name pvName = new Name("harnessPv");
            final LocationVariable pv = new LocationVariable(
                new de.uka.ilkd.key.logic.ProgramElementName(pvName.toString()),
                services.getJavaInfo().getKeYJavaType("int"));
            goal.addProgramVariable(pv);

            assertNotNull(goal.getLocalNamespaces().programVariables().lookup(pvName),
                "added program variable must be in the goal-local namespace");
            assertNull(sibling.getLocalNamespaces().programVariables().lookup(pvName),
                "added program variable must not leak to the sibling goal");
            assertNull(services.getNamespaces().programVariables().lookup(pvName),
                "added program variable must not leak into the proof-global namespace");
        } finally {
            env.dispose();
        }
    }

    // ------------------------------------------------------------------------ recorder priority

    /**
     * A name proposal recorded for replay (saved proofs) must take absolute priority over any
     * generated name — the saved-proof compatibility contract every naming scheme must honour.
     */
    @Test
    public void recordedProposalOverridesGeneratedName() throws Exception {
        final KeYEnvironment<?> env = load("skolemSiblings.key");
        try {
            final Proof proof = env.getLoadedProof();
            final Services services = proof.getServices();
            final Name recorded = new Name("replayedName");
            services.getNameRecorder()
                    .setProposals(ImmutableList.of(recorded));
            final String minted = services.getTermBuilder().newName("whatever");
            assertEquals(recorded.toString(), minted,
                "a recorded proposal must win over generated names");
        } finally {
            env.dispose();
        }
    }

    // -------------------------------------------------------- saved-proof format compatibility

    /**
     * Frozen saved proof (checked-in resource) that APPLIES an added rule by its recorded name
     * ({@code insert_hidden_taclet1_0}). Added-rule names are replayed by REGENERATION (the
     * replayer looks the recorded name up in the goal-local taclet index -- see
     * {@code IntermediateProofReplayer}), not via the {@code NameRecorder}: any change to the
     * added-rule name format therefore breaks loading of every existing proof unless it ships
     * with a name conversion in the replayer. This test pins that compatibility.
     */
    @Test
    public void savedProofWithHiddenTacletReplays() throws Exception {
        final KeYEnvironment<?> env = load("insertHidden.proof");
        try {
            final Proof proof = env.getLoadedProof();
            boolean hiddenApplied = false;
            final var it = proof.root().subtreeIterator();
            while (it.hasNext()) {
                final var node = it.next();
                if (node.getAppliedRuleApp() != null && node.getAppliedRuleApp().rule().name()
                        .toString().startsWith("insert_hidden")) {
                    hiddenApplied = true;
                }
            }
            assertTrue(hiddenApplied,
                "the saved insert_hidden application must have been replayed");
        } finally {
            env.dispose();
        }
    }

    // ------------------------------------------------------------------- MT-strict variant

    /**
     * The same locality/reproducibility invariants under the MULTI-CORE prover: skolem names on a
     * goal must be a pure function of that goal's branch state, independent of which worker ran
     * it (#3851; formerly violated by per-worker {@code __t<w>} name tags).
     */
    private static final int MT_WORKERS = 8;

    @Test
    public void skolemNamesAreWorkerIndependent() throws Exception {
        final List<String> seq = runSkolemScenario(0);
        final List<String> mt = runSkolemScenario(MT_WORKERS);
        assertEquals(seq, mt,
            "skolem names must not depend on the worker/scheduling that produced them");
    }

    /**
     * Runs the sibling-skolemization scenario and returns the per-goal {@code idx} skolem names.
     * {@code workers == 0} hand-applies the split+skolemize on the calling thread (the sequential
     * baseline). {@code workers > 0} pins the two-goal shape with a deterministic {@code andRight}
     * split and then drives the {@code allRight} skolemization through {@link ProofStarter}, which
     * selects the {@link ParallelProver} from the system properties -- so the fresh names are
     * genuinely minted under the multi-core prover, not just under a flag that nothing reads.
     */
    private List<String> runSkolemScenario(int workers) throws Exception {
        final String prop = ParallelProver.PARALLEL_PROPERTY;
        final String threads = ParallelProver.THREADS_PROPERTY;
        final String oldProp = System.getProperty(prop);
        final String oldThreads = System.getProperty(threads);
        final KeYEnvironment<?> env = load("skolemSiblings.key");
        try {
            final Proof proof = env.getLoadedProof();
            if (workers == 0) {
                System.setProperty(prop, "false");
                splitAndSkolemize(proof);
            } else {
                System.setProperty(prop, "true");
                System.setProperty(threads, Integer.toString(workers));
                // guard against a silently single-core run: the parallel prover must actually be
                // selected and the worker count honoured exactly, so the skolemization below runs
                // on more than one worker even on a low-core machine
                assertTrue(ParallelProver.isEnabled(),
                    "parallel prover must be enabled for the multi-worker run");
                assertEquals(workers, ParallelProver.effectiveWorkerCount(),
                    "the multi-worker run must use exactly the requested worker count");
                assertTrue(ParallelProver.effectiveWorkerCount() > 1,
                    "the worker-independence test is only meaningful with more than one worker");
                // fix the two sibling goals deterministically, then let the parallel prover apply
                // allRight (the only remaining rule) on each branch, minting the idx skolems
                applyOnFormula(proof, proof.openGoals().head(), "andRight", 1, false);
                final ProofStarter starter = new ProofStarter(false);
                starter.init(proof);
                starter.setMaxRuleApplications(1000);
                starter.start(proof.openGoals());
            }
            return skolemNamesPerGoal(proof, "idx");
        } finally {
            restore(prop, oldProp);
            restore(threads, oldThreads);
            env.dispose();
        }
    }

    /**
     * Under an MT run, a no-mint split must give each sibling goal its OWN {@code NamespaceSet}.
     * {@code Goal.split}/{@code clone} hand the siblings one shared set by reference, and
     * {@code adaptNamespacesNewGoals} de-aliases them per goal via {@code resetLocalSymbols}. If
     * that
     * de-aliasing is skipped for a no-mint split (the reverted D2 "no-mint skip" optimization), the
     * siblings keep aliasing one namespace, so a later skolem mint on one branch leaks into the
     * other -- the branch namespaces then diverge from a single-threaded reload and replay breaks.
     * This pins the sibling isolation directly, without depending on the rare race to manifest.
     */
    @Test
    public void mtNoMintSplitGivesEachSiblingItsOwnNamespaces() throws Exception {
        final KeYEnvironment<?> env = load("skolemSiblings.key");
        final var scope = ParallelProver.enterMultiThreadedRun();
        try {
            final Proof proof = env.getLoadedProof();
            assertTrue(ParallelProver.isMultiThreadedRunActive(),
                "the MT-run marker must be set for adaptNamespacesNewGoals to take the MT branch");
            // andRight is a purely propositional (no-mint) split of the root conjunction
            applyOnFormula(proof, proof.openGoals().head(), "andRight", 1, false);
            final ImmutableList<Goal> goals = proof.openGoals();
            assertEquals(2, goals.size(), "andRight must produce two sibling goals");
            final Goal a = goals.head();
            final Goal b = goals.tail().head();
            assertNotSame(a.getLocalNamespaces(), b.getLocalNamespaces(),
                "sibling goals of a no-mint MT split must not share one NamespaceSet (D2 aliasing)");
            assertNotSame(a.getLocalNamespaces().functions(), b.getLocalNamespaces().functions(),
                "sibling function namespaces must be independent so skolem mints cannot leak across");
        } finally {
            scope.close();
            env.dispose();
        }
    }

    private static void restore(String key, String value) {
        if (value == null) {
            System.clearProperty(key);
        } else {
            System.setProperty(key, value);
        }
    }

    // ------------------------------------------------------------------------------- helpers

    /**
     * The skolem constants (0-ary functions) whose name contains {@code originStem}, one per open
     * goal, read from each goal's LOCAL function namespace.
     */
    private static List<String> skolemNamesPerGoal(Proof proof, String originStem) {
        final List<String> names = new ArrayList<>();
        for (final Goal g : proof.openGoals()) {
            final List<String> perGoal = new ArrayList<>();
            // the node-local symbol storage is the authoritative record of what this branch
            // introduced (the goal-local namespaces are rebuilt from it)
            for (final Function f : g.node().getLocalFunctions()) {
                if (f.arity() == 0 && f.name().toString().contains(originStem)) {
                    perGoal.add(f.name().toString());
                }
            }
            assertEquals(1, perGoal.size(),
                "expected exactly one '" + originStem + "' skolem per goal, got " + perGoal);
            names.add(perGoal.get(0));
            // and it must be resolvable through the goal-local namespaces
            assertNotNull(
                g.getLocalNamespaces().functions().lookup(new Name(perGoal.get(0))),
                "skolem must be visible through the goal-local namespace: " + perGoal.get(0));
        }
        return names;
    }

    private static List<NoPosTacletApp> localRules(Goal g) {
        final List<NoPosTacletApp> rules = new ArrayList<>();
        for (final NoPosTacletApp app : g.node().getLocalIntroducedRules()) {
            rules.add(app);
        }
        return rules;
    }

    /** andRight on the root conjunction, then allRight on each branch (skolemizes 'idx'). */
    private static void splitAndSkolemize(Proof proof) {
        applyOnFormula(proof, proof.openGoals().head(), "andRight", 1, false);
        for (final Goal g : proof.openGoals()) {
            applyOnFormula(proof, g, "allRight", 1, false);
        }
    }

    /**
     * andRight, then on the (b -> b) branch impRight and hide_left on the antecedent b. The
     * other branch stays untouched (the sibling witness).
     */
    /** Exposed for the one-off proof-resource generator. */
    static void splitAndHideForGenerator(Proof proof) {
        splitAndHide(proof);
    }

    private static void splitAndHide(Proof proof) {
        applyOnFormula(proof, proof.openGoals().head(), "andRight", 1, false);
        // the impRight-able branch is the one whose succedent formula is an implication
        Goal impGoal = null;
        for (final Goal g : proof.openGoals()) {
            if (g.sequent().succedent().getFirst().formula().op().name().toString()
                    .equals("imp")) {
                impGoal = g;
            }
        }
        assertNotNull(impGoal, "expected the (b -> b) branch");
        applyOnFormula(proof, impGoal, "impRight", 1, false);
        // after impRight the goal has antecedent [b], succedent [b]; hide the antecedent b
        applyOnFormula(proof, impGoal, "hide_left", 1, true);
    }

    /**
     * Applies the named taclet to the top level of the given (1-based) formula of the goal,
     * on the antecedent or succedent side.
     */
    private static void applyOnFormula(Proof proof, Goal goal, String tacletName, int formulaNr,
            boolean inAntec) {
        final var taclet =
            proof.getInitConfig().lookupActiveTaclet(new Name(tacletName));
        assertNotNull(taclet, "taclet not found: " + tacletName);
        final int nr = inAntec ? formulaNr
                : goal.sequent().antecedent().size() + formulaNr;
        final PosInOccurrence pio = new PosInOccurrence(
            goal.sequent().getFormulaByNr(nr), PosInTerm.getTopLevel(), inAntec);
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(taclet)
                .matchFind(pio, proof.getServices());
        assertNotNull(app, tacletName + " must match at the given position");
        app = app.setPosInOccurrence(pio, proof.getServices());
        app = app.tryToInstantiate(
            proof.getServices().getOverlay(goal.getLocalNamespaces()));
        assertNotNull(app, tacletName + " must be instantiable");
        goal.apply(app);
    }

    private static KeYEnvironment<?> load(String file) throws Exception {
        return KeYEnvironment.load(JavaProfile.getDefaultInstance(),
            NAMING_DIR.resolve(file), null, null, null, true);
    }
}
