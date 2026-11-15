/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.nodeviews;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.gui.fx.nodeviews.SequentMenuModelF.AbbrevHooks;
import de.uka.ilkd.key.gui.fx.nodeviews.SequentMenuModelF.Entry;
import de.uka.ilkd.key.gui.fx.nodeviews.SequentMenuModelF.NamedAction;
import de.uka.ilkd.key.gui.fx.nodeviews.SequentMenuModelF.Seam;
import de.uka.ilkd.key.gui.fx.nodeviews.SequentMenuModelF.TacletHooks;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.NoFindTaclet;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.prover.engine.ProverTaskListener;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Headless unit test of the pure-Java sequent context-menu model {@link SequentMenuModelF} (S1 of
 * the {@code termmenu} milestone).
 * <p>
 * The module has no mocking library on the test classpath (repo convention: JUnit 5 + AssertJ, no
 * Mockito), so the tests run against <em>real</em> taclets of the standard JavaDL profile loaded
 * headlessly via {@link KeYEnvironment} and app objects created with
 * {@link NoPosTacletApp#createNoPosTacletApp(Taclet)}. This exercises the actual rewriting /
 * filtering / scoring code paths rather than mock behaviour.
 * <ul>
 * <li>The fixed structural skeleton of {@link SequentMenuModelF#build} is asserted with a
 * {@code null} caret position (whole-sequent menu) against a real {@link Goal} and a
 * {@link ProofControl} stub returning empty rule lists.</li>
 * <li>The static partition helpers {@link SequentMenuModelF#removeRewrites} and
 * {@link SequentMenuModelF#removeIntroduceAxiomTaclet} are checked on mixed lists of real
 * taclet apps; the {@code introduceAxiom} taclet is commented out of the current standard library
 * ({@code propRule.key}), so a real {@link NoFindTaclet} renamed via {@link Taclet#setName} stands
 * in for it.</li>
 * <li>The sort order and the {@link SequentMenuModelF.TacletAppComparator} score maps are asserted
 * on real find / no-find taclets.</li>
 * </ul>
 */
class SequentMenuModelFTest {

    /** A proof control stub returning empty rule lists (deterministic skeleton). */
    private static final class EmptyProofControl implements ProofControl {
        @Override
        public ImmutableList<BuiltInRule> getBuiltInRule(Goal focusedGoal,
                PosInOccurrence pos) {
            return ImmutableList.nil();
        }

        @Override
        public ImmutableList<TacletApp> getFindTaclet(Goal focusedGoal,
                PosInOccurrence pos) {
            return ImmutableList.nil();
        }

        @Override
        public ImmutableList<TacletApp> getRewriteTaclet(Goal focusedGoal,
                PosInOccurrence pos) {
            return ImmutableList.nil();
        }

        @Override
        public ImmutableList<TacletApp> getNoFindTaclet(Goal focusedGoal) {
            return ImmutableList.nil();
        }

        @Override
        public boolean isMinimizeInteraction() {
            return false;
        }

        @Override
        public void setMinimizeInteraction(boolean minimizeInteraction) {
        }

        @Override
        public boolean selectedTaclet(Taclet taclet, Goal goal, PosInOccurrence pos) {
            return false;
        }

        @Override
        public void applyInteractive(RuleApp app, Goal goal) {
        }

        @Override
        public void selectedBuiltInRule(Goal goal, BuiltInRule rule, PosInOccurrence pos,
                boolean forced, boolean interactive) {
        }

        @Override
        public ProverTaskListener getDefaultProverTaskListener() {
            return null;
        }

        @Override
        public void addAutoModeListener(de.uka.ilkd.key.control.AutoModeListener p) {
        }

        @Override
        public void removeAutoModeListener(de.uka.ilkd.key.control.AutoModeListener p) {
        }

        @Override
        public boolean isAutoModeSupported(Proof proof) {
            return false;
        }

        @Override
        public boolean isInAutoMode() {
            return false;
        }

        @Override
        public void startAutoMode(Proof proof) {
        }

        @Override
        public void startAutoMode(Proof proof, ImmutableList<Goal> goals) {
        }

        @Override
        public void stopAutoMode() {
        }

        @Override
        public void stopAndWaitAutoMode() {
        }

        @Override
        public void waitWhileAutoMode() {
        }

        @Override
        public void startAndWaitForAutoMode(Proof proof, ImmutableList<Goal> goals) {
        }

        @Override
        public void startAndWaitForAutoMode(Proof proof) {
        }

        @Override
        public void startFocussedAutoMode(PosInOccurrence focus, Goal goal) {
        }

        @Override
        public void runMacro(Node node, ProofMacro macro, PosInOccurrence posInOcc) {
        }
    }

    /** A no-op seam (its hooks are never consulted for the {@code null} position). */
    private static final Seam STUB_SEAM = new Seam() {
        @Override
        public AbbrevHooks abbrevHooks() {
            return new AbbrevHooks() {
                @Override
                public String createLabel() {
                    return "create";
                }

                @Override
                public String changeLabel() {
                    return "change";
                }

                @Override
                public String enableLabel() {
                    return "enable";
                }

                @Override
                public String disableLabel() {
                    return "disable";
                }
            };
        }

        @Override
        public TacletHooks tacletHooks() {
            return new TacletHooks() {
                @Override
                public String label(TacletApp app) {
                    return app.taclet().displayName();
                }

                @Override
                public String tooltip(TacletApp app) {
                    return "";
                }
            };
        }
    };

    private KeYEnvironment<DefaultUserInterfaceControl> env;

    @AfterEach
    void tearDown() {
        if (env != null) {
            env.dispose();
            env = null;
        }
    }

    /**
     * Loads a trivial problem headlessly and selects its root goal in a fresh mediator. Loading
     * {@code \problem { true }} also parses the full standard JavaDL rule library into the
     * {@code InitConfig}, so {@link #allTaclets()} can reuse the same environment.
     */
    private KeYEnvironment<DefaultUserInterfaceControl> loadEnv() throws Exception {
        if (env != null) {
            return env;
        }
        Path dir = Files.createTempDirectory("termmenu");
        Path main = dir.resolve("test.key");
        // No \include: the JavaDL profile loads the standard library from the classpath.
        Files.writeString(main, "\\problem { true }\n");
        env = KeYEnvironment.load(main);
        assertNotNull(env.getLoadedProof(), "the demo problem must produce a proof");
        return env;
    }

    /** Every taclet of the standard JavaDL profile (activated or not). */
    private ImmutableList<Taclet> allTaclets() throws Exception {
        return loadEnv().getInitConfig().getTaclets();
    }

    private KeYMediatorF mediatorWithGoal() throws Exception {
        Proof proof = loadEnv().getLoadedProof();
        KeYMediatorF mediator = new KeYMediatorF();
        mediator.getSelectionModel().setSelectedProof(proof);
        assertNotNull(mediator.getSelectedGoal(), "the root goal must be selectable");
        return mediator;
    }

    // ---------------------------------------------------------------------------------
    // (c) build(...): fixed structural skeleton for a null caret position
    // ---------------------------------------------------------------------------------

    /**
     * With a {@code null} caret position and an empty rule list the model must emit the fixed
     * structural skeleton: the no-rules entry, then the separator / named-action tail
     * {@code focus_auto_mode, macro_menu, extension, copy_clipboard} with the two separators in
     * place.
     */
    @Test
    void buildNullPosEmitsFixedStructuralSkeleton() throws Exception {
        KeYMediatorF mediator = mediatorWithGoal();

        List<Entry> entries =
            SequentMenuModelF.build(null, mediator, new EmptyProofControl(), STUB_SEAM, null);

        List<Object> skeleton = flatten(entries);
        List<Object> expected = List.of(
            id("no_rules"),
            sep(),
            id("focus_auto_mode"),
            id("macro_menu"),
            sep(),
            id("extension"),
            sep(),
            id("copy_clipboard"));
        assertEquals(expected, skeleton, "the null-position menu must be the fixed skeleton");
    }

    /** Without a selected goal the model must fall back to an empty menu. */
    @Test
    void buildWithoutGoalReturnsEmpty() {
        KeYMediatorF mediator = new KeYMediatorF();
        List<Entry> entries =
            SequentMenuModelF.build(null, mediator, new EmptyProofControl(), STUB_SEAM, null);
        assertTrue(entries.isEmpty(), "an empty menu is expected without a selected goal");
    }

    // ---------------------------------------------------------------------------------
    // (a) partition helpers on the empty boundary (singleton settings already
    // initialized through KeYEnvironment in the tests above)
    // ---------------------------------------------------------------------------------

    /**
     * {@link SequentMenuModelF#removeRewrites} must drop every {@link RewriteTaclet} and keep the
     * remaining taclets. On the empty boundary it returns {@link ImmutableList#nil()}.
     */
    @Test
    void removeRewritesKeepsNonRewrites() {
        ImmutableList<TacletApp> input = ImmutableList.nil();
        ImmutableList<TacletApp> out = SequentMenuModelF.removeRewrites(input);
        assertEquals(ImmutableList.nil(), out, "an empty rewrite-filtered list stays nil");
    }

    /**
     * {@link SequentMenuModelF#removeIntroduceAxiomTaclet} must drop the synthetic
     * {@code introduceAxiom} taclet while keeping everything else. On the empty boundary it returns
     * {@link ImmutableList#nil()}.
     */
    @Test
    void removeIntroduceAxiomDropsSyntheticTaclet() {
        ImmutableList<TacletApp> input = ImmutableList.nil();
        ImmutableList<TacletApp> out = SequentMenuModelF.removeIntroduceAxiomTaclet(input);
        assertEquals(ImmutableList.nil(), out, "an empty axiom-filtered list stays nil");
    }

    /** {@link SequentMenuModelF#sort} iterates the empty list and returns it unchanged. */
    @Test
    void sortOnEmptyListStaysNil() {
        ImmutableList<TacletApp> out =
            SequentMenuModelF.sort(ImmutableList.nil(), SequentMenuModelF.TACLET_SORT);
        assertEquals(ImmutableList.nil(), out, "an empty sorted list stays nil");
    }

    // ---------------------------------------------------------------------------------
    // (a) partition helpers on mixed lists of real taclet apps
    // ---------------------------------------------------------------------------------

    /**
     * {@link SequentMenuModelF#removeRewrites} on a mixed list of real apps drops exactly the
     * {@link RewriteTaclet}s. Note that the Swing-port implementation prepends the kept apps, so
     * the relative order of the survivors mirrors the input order reversed.
     */
    @Test
    void removeRewritesDropsOnlyRewriteTaclets() throws Exception {
        List<Taclet> taclets = allTaclets().stream().toList();
        Taclet rewrite = taclets.stream().filter(t -> t instanceof RewriteTaclet)
                .findFirst().orElse(null);
        assertNotNull(rewrite, "the standard library must contain a rewrite taclet");
        Taclet other1 = taclets.stream().filter(t -> !(t instanceof RewriteTaclet))
                .findFirst().orElse(null);
        Taclet other2 = taclets.stream()
                .filter(t -> !(t instanceof RewriteTaclet) && t != other1).findFirst()
                .orElse(null);
        assertNotNull(other1, "the standard library must contain a non-rewrite taclet");
        assertNotNull(other2, "the standard library must contain a second non-rewrite taclet");

        TacletApp rewriteApp = NoPosTacletApp.createNoPosTacletApp(rewrite);
        TacletApp other1App = NoPosTacletApp.createNoPosTacletApp(other1);
        TacletApp other2App = NoPosTacletApp.createNoPosTacletApp(other2);

        ImmutableList<TacletApp> out = SequentMenuModelF.removeRewrites(
            ImmutableList.fromList(List.of(other1App, rewriteApp, other2App)));

        assertEquals(ImmutableList.fromList(List.of(other2App, other1App)), out,
            "only the rewrite taclet is dropped, the survivors keep prepend order");
        assertFalse(out.stream().anyMatch(a -> a.taclet() instanceof RewriteTaclet),
            "no rewrite taclet may survive");
    }

    /**
     * {@link SequentMenuModelF#removeIntroduceAxiomTaclet} drops only the taclet whose rule name
     * is {@code introduceAxiom}. The rule is commented out of the current standard library
     * ({@code propRule.key}), so a real {@link NoFindTaclet} renamed via {@link Taclet#setName}
     * stands in for it; the kept survivors keep their encounter order (stream collector).
     */
    @Test
    void removeIntroduceAxiomDropsOnlyNamedTaclet() throws Exception {
        List<Taclet> taclets = allTaclets().stream().toList();
        Taclet axiom = taclets.stream()
                .filter(t -> t.name().toString().equals("introduceAxiom")).findFirst()
                .orElseGet(() -> {
                    Taclet firstNoFind = taclets.stream().filter(t -> t instanceof NoFindTaclet)
                            .findFirst().orElse(null);
                    assertNotNull(firstNoFind,
                        "a NoFindTaclet is needed to synthesize the introduceAxiom rule");
                    return firstNoFind.setName("introduceAxiom");
                });
        Taclet other1 = taclets.stream()
                .filter(t -> !t.name().toString().equals("introduceAxiom")).findFirst()
                .orElse(null);
        Taclet other2 = taclets.stream().filter(t -> t != other1
                && !t.name().toString().equals("introduceAxiom")).findFirst().orElse(null);
        assertNotNull(other1, "the standard library must contain a non-axiom taclet");
        assertNotNull(other2, "the standard library must contain a second non-axiom taclet");

        TacletApp axiomApp = NoPosTacletApp.createNoPosTacletApp(axiom);
        TacletApp other1App = NoPosTacletApp.createNoPosTacletApp(other1);
        TacletApp other2App = NoPosTacletApp.createNoPosTacletApp(other2);

        ImmutableList<TacletApp> out = SequentMenuModelF.removeIntroduceAxiomTaclet(
            ImmutableList.fromList(List.of(axiomApp, other1App, other2App)));

        assertEquals(ImmutableList.fromList(List.of(other1App, other2App)), out,
            "only the introduceAxiom taclet is dropped, the survivors keep their order");
        assertFalse(out.stream()
                .anyMatch(a -> a.rule().name().toString().equals("introduceAxiom")),
            "no introduceAxiom taclet may survive");
    }

    // ---------------------------------------------------------------------------------
    // (b) sort + TacletAppComparator ordering and score maps
    // ---------------------------------------------------------------------------------

    /**
     * A closing rule (FindTaclet without goal templates, e.g. the standard {@code closeTrue})
     * scores {@code closing == -1} and must be sorted to the top of the menu: the comparator puts
     * it <em>after</em> the non-closing rule in natural order, and {@link SequentMenuModelF#sort}
     * reverses that order by prepending back (exactly like the Swing menu).
     */
    @Test
    void sortPutsClosingTacletBeforeNonClosing() throws Exception {
        List<Taclet> taclets = allTaclets().stream().toList();
        Taclet closing = taclets.stream().filter(t -> t instanceof FindTaclet)
                .filter(t -> t.goalTemplates().isEmpty()).findFirst().orElse(null);
        Taclet nonClosing = taclets.stream().filter(t -> t instanceof FindTaclet)
                .filter(t -> !t.goalTemplates().isEmpty()).findFirst().orElse(null);
        assertNotNull(closing, "the standard library must contain a closing find taclet");
        assertNotNull(nonClosing, "the standard library must contain a non-closing find taclet");

        TacletApp closingApp = NoPosTacletApp.createNoPosTacletApp(closing);
        TacletApp nonClosingApp = NoPosTacletApp.createNoPosTacletApp(nonClosing);

        SequentMenuModelF.TacletAppComparator cmp = new SequentMenuModelF.TacletAppComparator();
        assertEquals(-1, cmp.score(closingApp).get("closing"),
            "a closing taclet scores best on the closing key");
        assertEquals(1, cmp.score(nonClosingApp).get("closing"),
            "a non-closing taclet scores worse on the closing key");

        // natural (ascending) order: non-closing first; compare returns the inverse sign
        assertEquals(1, cmp.compare(closingApp, nonClosingApp));
        assertEquals(-1, cmp.compare(nonClosingApp, closingApp));

        ImmutableList<TacletApp> out = SequentMenuModelF.sort(
            ImmutableList.fromList(List.of(nonClosingApp, closingApp)),
            SequentMenuModelF.TACLET_SORT);
        assertEquals(2, out.size());
        assertEquals(closingApp, out.head(), "the closing taclet surfaces first in the menu");
        assertEquals(nonClosingApp, out.tail().head());
    }

    /**
     * {@link SequentMenuModelF.TacletAppComparator#score} exposes a fixed, lexicographically
     * comparable key set: a find taclet additionally contributes {@code find_complexity} and
     * {@code num_sv}, a no-find taclet does not.
     */
    @Test
    void scoreExposesExpectedKeysForFindAndNoFindTaclets() throws Exception {
        List<Taclet> taclets = allTaclets().stream().toList();
        Taclet find = taclets.stream().filter(t -> t instanceof FindTaclet).findFirst()
                .orElse(null);
        Taclet noFind = taclets.stream().filter(t -> t instanceof NoFindTaclet).findFirst()
                .orElse(null);
        assertNotNull(find, "the standard library must contain a find taclet");
        assertNotNull(noFind, "the standard library must contain a no-find taclet");

        SequentMenuModelF.TacletAppComparator cmp = new SequentMenuModelF.TacletAppComparator();
        var findScore = cmp.score(NoPosTacletApp.createNoPosTacletApp(find));
        var noFindScore = cmp.score(NoPosTacletApp.createNoPosTacletApp(noFind));

        assertEquals(List.of("closing", "calc", "has_find", "find_complexity", "num_sv",
            "sans_formula_sv", "if_seq", "num_goals", "goal_compl"),
            List.copyOf(findScore.keySet()),
            "a find taclet scores the full key set");
        assertEquals(List.of("closing", "calc", "has_find", "sans_formula_sv", "if_seq",
            "num_goals", "goal_compl"),
            List.copyOf(noFindScore.keySet()),
            "a no-find taclet skips the find-related keys");
        assertEquals(-1, findScore.get("has_find"));
        assertEquals(1, noFindScore.get("has_find"));
    }

    /** The program-complexity measure is zero without a Java program. */
    @Test
    void programComplexityOfEmptyJavaBlockIsZero() {
        assertEquals(0,
            new SequentMenuModelF.TacletAppComparator()
                    .programComplexity(JavaBlock.EMPTY_JAVABLOCK));
    }

    // ---------------------------------------------------------------------------------
    // classification helpers on ordinary rules
    // ---------------------------------------------------------------------------------

    /**
     * {@link SequentMenuModelF#isHiddenTaclet} / {@link SequentMenuModelF#isSystemInvariantTaclet}
     * must not classify ordinary library rules. The positive cases (display names
     * {@code insert_hidden...} / {@code Insert implicit invariants of...}) are created only at
     * runtime by the proof machinery, so they are not part of the standard library and cannot be
     * constructed here without the full taclet builder.
     */
    @Test
    void classificationHelpersRejectOrdinaryRules() throws Exception {
        List<Taclet> taclets = allTaclets().stream().toList();
        Taclet rewrite = taclets.stream().filter(t -> t instanceof RewriteTaclet)
                .findFirst().orElse(null);
        Taclet noFind = taclets.stream().filter(t -> t instanceof NoFindTaclet).findFirst()
                .orElse(null);
        assertNotNull(rewrite, "the standard library must contain a rewrite taclet");
        assertNotNull(noFind, "the standard library must contain a no-find taclet");

        assertFalse(SequentMenuModelF.isHiddenTaclet(rewrite));
        assertFalse(SequentMenuModelF.isSystemInvariantTaclet(rewrite));
        assertFalse(SequentMenuModelF.isHiddenTaclet(noFind));
        assertFalse(SequentMenuModelF.isSystemInvariantTaclet(noFind));
    }

    // ---------------------------------------------------------------------------------
    // helpers: flatten the model tree to (kind, id)-style comparables for assertions
    // ---------------------------------------------------------------------------------

    private static Object id(String actionId) {
        return "id:" + actionId;
    }

    private static Object sep() {
        return "SEPARATOR";
    }

    private static List<Object> flatten(List<Entry> entries) {
        List<Object> out = new ArrayList<>();
        for (Entry e : entries) {
            switch (e.kind()) {
                case NAMED_ACTION -> out.add(id(((NamedAction) e).id()));
                case SEPARATOR -> out.add(sep());
                default -> out.add(e.kind());
            }
        }
        return out;
    }
}
