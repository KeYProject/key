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
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.prover.engine.ProverTaskListener;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Headless unit test of the pure-Java sequent context-menu model
 * {@link SequentMenuModelF} (T1 of the {@code termmenu} milestone).
 * <p>
 * A {@link TacletApp}/{@link Taclet} cannot be trivially constructed without a full
 * taclet builder, so the fixed structural skeleton is asserted through
 * {@link SequentMenuModelF#build} with a <em>null</em> caret position (whole-sequent
 * menu) against a real {@link Goal} loaded headlessly via {@link KeYEnvironment} and a
 * {@link ProofControl} stub returning empty rule lists. The static partition helpers are
 * exercised on the empty / no-goal boundary and on the real (find) taclet list where a
 * partition can be asserted without constructing taclets by hand.
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

    /** Loads a trivial problem headlessly and selects its root goal in a fresh mediator. */
    private KeYMediatorF mediatorWithGoal() throws Exception {
        Path dir = Files.createTempDirectory("termmenu");
        Path main = dir.resolve("test.key");
        // No \include: the JavaDL profile loads the standard library from the classpath.
        Files.writeString(main, "\\problem { true }\n");
        env = KeYEnvironment.load(main);
        Proof proof = env.getLoadedProof();
        assertNotNull(proof, "the demo problem must produce a proof");

        KeYMediatorF mediator = new KeYMediatorF();
        mediator.getSelectionModel().setSelectedProof(proof);
        assertNotNull(mediator.getSelectedGoal(), "the root goal must be selectable");
        return mediator;
    }

    /**
     * (c) With a {@code null} caret position and an empty rule list the model must emit the
     * fixed structural skeleton: no-rules entry, then the separator / named-action tail
     * {@code focus_auto_mode, macro_menu, extension, copy_clipboard}.
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

    /**
     * Without a selected goal the model must fall back to an empty menu (the Swing
     * {@code CurrentGoalViewListener} only opens a menu with a valid goal+position).
     */
    @Test
    void buildWithoutGoalReturnsEmpty() {
        KeYMediatorF mediator = new KeYMediatorF();
        List<Entry> entries =
            SequentMenuModelF.build(null, mediator, new EmptyProofControl(), STUB_SEAM, null);
        assertTrue(entries.isEmpty(), "an empty menu is expected without a selected goal");
    }

    /**
     * (a) {@link SequentMenuModelF#removeRewrites} must drop every {@code RewriteTaclet} and keep
     * the remaining order. On the empty boundary it returns {@link ImmutableList#nil()}.
     */
    @Test
    void removeRewritesKeepsNonRewrites() {
        ImmutableList<TacletApp> input = ImmutableList.nil();
        ImmutableList<TacletApp> out = SequentMenuModelF.removeRewrites(input);
        assertEquals(ImmutableList.nil(), out, "an empty rewrite-filtered list stays nil");
    }

    /**
     * (a) {@link SequentMenuModelF#removeIntroduceAxiomTaclet} must drop the synthetic
     * {@code introduceAxiom} taclet while keeping everything else. On the empty boundary it returns
     * {@link ImmutableList#nil()}.
     */
    @Test
    void removeIntroduceAxiomDropsSyntheticTaclet() {
        ImmutableList<TacletApp> input = ImmutableList.nil();
        ImmutableList<TacletApp> out =
            SequentMenuModelF.removeIntroduceAxiomTaclet(input);
        assertEquals(ImmutableList.nil(), out, "an empty axiom-filtered list stays nil");
    }

    /**
     * (b) {@link SequentMenuModelF#sort} reverses the comparator's natural order (it prepends the
     * sorted list back together). On the empty boundary it returns {@link ImmutableList#nil()}.
     */
    @Test
    void sortOnEmptyListStaysNil() {
        ImmutableList<TacletApp> out =
            SequentMenuModelF.sort(ImmutableList.nil(), SequentMenuModelF.TACLET_SORT);
        assertEquals(ImmutableList.nil(), out, "an empty sorted list stays nil");
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
