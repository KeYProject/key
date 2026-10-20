/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.jvm.rule;

import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.ast.SourceElement;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.macros.DefaultAutoMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;

import org.key_project.jvm.Transpiler;
import org.key_project.jvm.profile.JvmProfile;
import org.key_project.logic.op.Modality;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * M3 backward-loop gate. The transpiler keeps javac loops fully linear — the restart jump of a
 * loop is a <em>backward</em> {@code jvm.Local.goto_(pc)} call (§3.4's structured {@code while}
 * emission is a planned optimization, not the shipped behavior; see
 * {@code TranspileTest#transpiledLoopKeepsBackwardGotoCanonicalShape}). The proof-side story of
 * this boundary, pinned here on live proofs, is:
 * <ul>
 * <li>{@link GotoRestoreRule} <em>is</em> auto-applied (the draft behavior of "interactive-only"
 * was wrong): the strategy unrolls the restored label suffix and drives through the loop. A
 * <em>bounded</em> backward loop therefore closes under auto mode exactly like the forward
 * {@code goto_} loops of {@code golden/Max.java} close via {@link GotoSpliceRule}
 * ({@link #boundedDoWhileLoopTerminatesMainLineUnderAuto}); the unrolling mechanics are pinned shape-wise
 * in {@link #restoreRuleUnrollsTheLabelSuffixOnTheLiveLoop}.</li>
 * <li>For {@code Sum}/{@code Restore} — loops whose termination bound is not statically
 * reachable — auto mode does <em>not</em> get stuck on the jump: it consumes the program and
 * leaves the createdness/arithmetic residual goals open (KeY's repeated-state anti-looping keeps
 * the unrolling bounded), which {@link #autoModeDrivesThroughLoopsWithoutLeavingAnActiveJump}
 * and {@link #infiniteLoopRestoreLeavesTheProofOpen} pin.</li>
 * </ul>
 */
class LoopProofTest {

    @TempDir
    Path tmpDir;

    /**
     * The bounded {@code do {} while} of {@code golden/Three.java} is driven to normal
     * termination by auto mode: three symbolic unrollings via {@code GotoRestoreRule}, then the
     * straight-line exit path runs to the {@code return} and the main-line modality empties.
     * The proof does <em>not</em> close because the anon-heap createdness residuals of the
     * {@code jvm.Local} contracts (the §9.1(2) family) stay open — the same residual family the
     * switch/literal/category-2 gates pin. What is pinned here is that the loop is no roadblock:
     * the main line terminates and no open goal carries a modality or an active jump.
     * (Contrast: {@code Max}'s forward {@code goto_} analog resolves without restore-driven
     * unrolling, so those residuals reduce far enough for the gate to close.)
     */
    @Test
    void boundedDoWhileLoopTerminatesMainLineUnderAuto() throws Exception {
        KeYEnvironment<DefaultUserInterfaceControl> env = setup("Three", "Three", "sum3()");
        try {
            runAuto(env, 600_000);
            assertThat(env.getLoadedProof().closed())
                    .as("createdness residuals (§9.1(2)) keep the proof open").isFalse();
            // the main line ran to the `return` and emptied the modality on that branch
            boolean emptiedModality = false;
            boolean restored = false;
            for (var it = env.getLoadedProof().root().subtreeIterator(); it.hasNext();) {
                var n = it.next();
                if (n.getAppliedRuleApp() == null) {
                    continue;
                }
                String rn = n.getAppliedRuleApp().rule().name().toString();
                if (rn.equals("emptyModality") || rn.equals("blockReturn")) {
                    emptiedModality = true;
                }
                if (rn.equals("JVM Goto Restore (backward)")) {
                    restored = true;
                }
            }
            assertThat(restored)
                    .as("the backward loop restart must have been restored").isTrue();
            assertThat(emptiedModality)
                    .as("the main line must terminate (return reached, modality emptied), "
                        + "with only the createdness residuals left open")
                    .isTrue();
            assertThat(env.getLoadedProof().openGoals().stream()
                    .noneMatch(LoopProofTest::hasModality))
                    .as("only modality-free residuals stay open").isTrue();
        } finally {
            env.dispose();
        }
    }

    /**
     * In {@code Three}'s proof, the exactly one {@code GotoRestoreRule} application is audited:
     * its premise has the backward {@code goto_(8)} as the active statement and its conclusion
     * re-enters the L8 suffix without the label guard — one semantic unrolling. (The proof
     * itself stays open on the §9.1(2) createdness residuals, see
     * {@link #boundedDoWhileLoopTerminatesMainLineUnderAuto}.)
     */
    @Test
    void restoreRuleUnrollsTheLabelSuffixOnTheLiveLoop() throws Exception {
        KeYEnvironment<DefaultUserInterfaceControl> env = setup("Three", "Three", "sum3()");
        try {
            runAuto(env, 600_000);
            Node restoreNode = null;
            for (var it = env.getLoadedProof().root().subtreeIterator(); it.hasNext();) {
                Node n = it.next();
                if (n.getAppliedRuleApp() != null && n.getAppliedRuleApp().rule().name()
                        .toString().equals("JVM Goto Restore (backward)")) {
                    assertThat(restoreNode).as("exactly one restore application expected").isNull();
                    restoreNode = n;
                }
            }
            assertThat(restoreNode).as("the backward goto_(8) must have been restored").isNotNull();

            assertThat(activeOfSequent(restoreNode.sequent()))
                    .as("the restore premise has the backward goto_ active")
                    .startsWith("jvm.Local.goto_(8)");
            var postIt = restoreNode.childrenIterator();
            assertThat(postIt).isNotNull();
            assertThat(postIt.hasNext()).isTrue();
            Node post = postIt.next();
            String conclusion = post.sequent().toString();
            assertThat(conclusion)
                    .as("the restored suffix re-enters the loop body without the label guard")
                    .contains("stk.push(local_1);")
                    .contains("stk.iadd();")
                    .contains("stk.top();")
                    .contains("jvm.Local.goto_(8);")
                    .contains("return stk.top();")
                    .doesNotContain("L8: { if (false) { break L8; }");
        } finally {
            env.dispose();
        }
    }

    /**
     * {@code Sum}'s {@code while} loop — whose exit is a symbolic {@code if}-split, so individual
     * iterations cannot all be resolved statically — is not a roadblock for auto mode: it drives
     * through the program and no open goal keeps a jump active (the strategy spends its budget on
     * the anon-heap createdness residuals, the §9.1(2) family, which stay open). This corrects the
     * docs' earlier, more specific claim that auto mode "stops at the backward {@code goto_}".
     */
    @Test
    void autoModeDrivesThroughLoopsWithoutLeavingAnActiveJump() throws Exception {
        KeYEnvironment<DefaultUserInterfaceControl> env = setup("Sum", "Sum", "whileSum(int)");
        try {
            runAuto(env, 600_000);
            // Focus auto on the modality-carrying goals only: the createdness-residual siblings
            // (no modality) eat the strategy budget, starving the main line. Generous budget so
            // the pinned shape is a rule boundary, not a budget artifact.
            ImmutableList<Goal> modalityGoals =
                env.getLoadedProof().openGoals().filter(LoopProofTest::hasModality);
            if (!modalityGoals.isEmpty()) {
                new DefaultAutoMacro().applyTo(env.getUi(), env.getLoadedProof(), modalityGoals,
                    null, env.getUi().getProofControl().getDefaultProverTaskListener());
            }
            ImmutableList<Goal> open = env.getLoadedProof().openGoals();
            assertThat(open).as("the transpiled loop leaves residual goals").isNotEmpty();
            // No open goal has an active jump of any kind: auto mode never stops "at the
            // backward goto_" (GotoRestoreRule is applied automatically).
            assertThat(open.stream().noneMatch(LoopProofTest::hasActiveGoto))
                    .as("auto mode must drive through the loop and leave no jump active")
                    .isTrue();
        } finally {
            env.dispose();
        }
    }

    /**
     * An <em>unbounded</em> backward loop (Restore's {@code do {} while (true)}) cannot close:
     * KeY's repeated-state anti-looping bounds the unrolling and the proof stays open on the
     * residual goals instead of silently proving the infinite loop terminating.
     */
    @Test
    void infiniteLoopRestoreLeavesTheProofOpen() throws Exception {
        KeYEnvironment<DefaultUserInterfaceControl> env = setup("Restore", "Restore", "spin()");
        try {
            runAuto(env, 600_000);
            assertThat(env.getLoadedProof().closed())
                    .as("the infinite backward loop must not be provably terminating").isFalse();
            assertThat(env.getLoadedProof().openGoals().stream()
                    .noneMatch(LoopProofTest::hasActiveGoto))
                    .as("no jump is left active; the residual goals are the bound")
                    .isTrue();
        } finally {
            env.dispose();
        }
    }

    // -- harness -----------------------------------------------------------------

    private KeYEnvironment<DefaultUserInterfaceControl> setup(String goldenClass,
            String className, String signature) throws Exception {
        // golden transpiler output + the local runtime, next to the key file
        try (InputStream in = getClass().getResourceAsStream("/golden/" + goldenClass + ".java")) {
            Files.copy(in, tmpDir.resolve(className + ".java"));
        }
        Path local = tmpDir.resolve("jvm/Local.java");
        Files.createDirectories(local.getParent());
        try (InputStream in =
            Transpiler.class.getResourceAsStream(Transpiler.LOCAL_RUNTIME_RESOURCE)) {
            Files.copy(in, local);
        }
        Path keyFile = tmpDir.resolve("proof.key");
        GotoProofTest.writeKeyFile(keyFile, className, signature);
        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(keyFile);
        assertThat(env.getLoadedProof().getServices().getProfile())
                .isSameAs(JvmProfile.INSTANCE);
        return env;
    }

    private static void runAuto(KeYEnvironment<DefaultUserInterfaceControl> env, long timeoutMs)
            throws Exception {
        // The createdness-residual sibling goals carry heavy anon-heap selectors; a tight budget
        // is eaten there before the main-line (modality-carrying) branch advances. Generous bound
        // so the pinned boundary is a rule boundary, not a budget artifact.
        env.getLoadedProof().getSettings().getStrategySettings().setTimeout(timeoutMs);
        new DefaultAutoMacro().applyTo(env.getUi(), env.getLoadedProof(),
            env.getLoadedProof().openGoals(), null,
            env.getUi().getProofControl().getDefaultProverTaskListener());
    }

    /** Is any succedent modality's active statement a {@code jvm.Local.goto_(…)} call? */
    private static boolean hasActiveGoto(Goal goal) {
        for (SequentFormula sf : goal.sequent().succedent()) {
            JTerm t = unwrapUpdate((JTerm) sf.formula());
            if (!(t.op() instanceof Modality)) {
                continue;
            }
            if (GotoSupport.isGotoCall(JavaTools.getActiveStatement(t.javaBlock()))) {
                return true;
            }
        }
        return false;
    }

    /** {@code true} if a succedent formula is a modality. */
    private static boolean hasModality(Goal goal) {
        for (SequentFormula sf : goal.sequent().succedent()) {
            if (unwrapUpdate((JTerm) sf.formula()).op() instanceof Modality) {
                return true;
            }
        }
        return false;
    }

    /** The active statement of the first succedent modality, or "{@code (no modality)}". */
    private static String activeOfSequent(org.key_project.prover.sequent.Sequent seq) {
        for (SequentFormula sf : seq.succedent()) {
            JTerm t = unwrapUpdate((JTerm) sf.formula());
            if (t.op() instanceof Modality) {
                SourceElement a = JavaTools.getActiveStatement(t.javaBlock());
                return String.valueOf(a);
            }
        }
        return "(no modality)";
    }

    private static JTerm unwrapUpdate(JTerm t) {
        return t.op() instanceof UpdateApplication ? UpdateApplication.getTarget(t) : t;
    }
}
