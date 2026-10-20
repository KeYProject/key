/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.jvm.rule;

import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.macros.DefaultAutoMacro;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.jvm.Transpiler;
import org.key_project.jvm.profile.JvmProfile;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * M3 category-2 (long/float/double) proof gates. {@code golden/Category2.java} carries the
 * exact transpiled shape of javac-17's real bytecode for the JVM's 64-bit/floating stack ops.
 * The per-§9.1(2) discriminator sharpens here: variable-only flows close when the result is
 * read back with <em>no</em> long arithmetic — {@code back} ({@code l2i}, pure cast flow) and
 * {@code flt} (pure float multiplication, no wrapping casts) — asserted <em>closed</em> under
 * {@code DefaultAutoMacro}. Everything else pins a residual: long <em>arithmetic</em>
 * ({@code ladd}) and int→long widening ({@code conv}) hit the {@code moduloLong}-normalization
 * gap (the any→long cast of {@code topL()}'s read wraps in {@code moduloLong} and auto never
 * reduces {@code moduloLong(add(a,b))} to {@code add(a,b)}); {@code lcmpish} materializes the
 * comparison sign −1/0/1 onto the stack (a literal, stuck on {@code moduloInt} normalization);
 * the double {@code ternary}'s boolean selector splits into the literals 1/0; and
 * {@code lconst} pushes a literal {@code 42L}. All four are pinned characterizations that
 * §9.1(2) covers.
 */
class Category2ProofTest {

    @TempDir
    Path tmpDir;

    @Test
    void backProofCloses() throws Exception {
        setupWorkspace();
        writeKeyFile(tmpDir.resolve("back.key"), "back(long)");
        assertProofCloses("back.key");
    }

    @Test
    void fltProofCloses() throws Exception {
        setupWorkspace();
        writeKeyFile(tmpDir.resolve("flt.key"), "flt(float,float)");
        assertProofCloses("flt.key");
    }

    /**
     * lcmpish does <em>not</em> close despite being variable-only: {@code lcmp} materializes the
     * comparison sign −1/0/1 as a literal on the {@code \\seq}, so the following {@code ifge}
     * branch predicate reads a constant — the §9.1(2) discriminator (constants in the stack
     * flow). The open goal gets stuck on the int-normalization of the sign:
     * {@code geq(moduloInt(Z(neglit(1))), Z(0))}, which auto mode never reduces (the int
     * {@code moduloInt} normalizer stops at negative literals). Pinned as characterization; see
     * §9.1(2).
     */
    @Test
    void lcmpishSignLiteralLeavesResidual() throws Exception {
        setupWorkspace();
        writeKeyFile(tmpDir.resolve("lcmpish.key"), "lcmpish(long,long)");
        assertProofOpenWith("lcmpish.key", "moduloInt");
    }

    /**
     * The double ternary is <em>also</em> residual, not closing: the boolean selector is pushed
     * as {@code stk.push((c ? 1 : 0));} (JVM booleans are ints; a bare {@code push(c)} would box
     * into {@code push(Object)} and lose the int semantics), and KeY's symbolic execution splits
     * the conditional into the literal branches {@code 1}/{@code 0} — every literal on the
     * {@code \\seq} opens the §9.1(2) {@code inRangeInt(literal)} residual in auto mode. The
     * double flow itself behaves ({@code flt} closes), only the boolean selector's literals
     * pin it here.
     */
    @Test
    void ternaryBooleanSelectorLeavesLiteralResidual() throws Exception {
        setupWorkspace();
        writeKeyFile(tmpDir.resolve("ternary.key"), "ternary(boolean,double,double)");
        assertProofOpenWith("ternary.key", "inRangeInt");
    }

    @Test
    void lconstLiteralFlowStaysOpenInAutoMode() throws Exception {
        setupWorkspace();
        writeKeyFile(tmpDir.resolve("lconst.key"), "lconst()");
        assertProofOpenAsResidual("lconst.key");
    }

    /**
     * ladd is variable-only, yet it does <em>not</em> close: the long addition's result is read
     * back through the any→long cast of {@code topL()}'s {@code \seq_get}, which KeY wraps in
     * {@code moduloLong}, and the default strategy never normalizes
     * {@code moduloLong(add(a,b))} to {@code add(a,b)} (no long-arithmetic normalizer analogous
     * to the int one). The open goal therefore carries the {@code moduloLong}-residue:
     * {@code equals(moduloLong(add(a,b)), result_topL)} vs.
     * {@code equals(result_topL, add(a,b))} in the succedent — pinned here and documented in
     * §9.1(2). Pure-cast long flows ({@code back}: {@code l2i}) and float/double flows
     * ({@code flt}) are unaffected and close.
     */
    @Test
    void laddLongAdditionLeavesModuloLongResidual() throws Exception {
        setupWorkspace();
        writeKeyFile(tmpDir.resolve("ladd.key"), "ladd(long,long)");
        assertProofOpenWith("ladd.key", "moduloLong");
    }

    @Test
    void convLongCastLeavesModuloLongResidual() throws Exception {
        setupWorkspace();
        writeKeyFile(tmpDir.resolve("conv.key"), "conv(int)");
        assertProofOpenWith("conv.key", "moduloLong");
    }

    private void assertProofCloses(String keyName) throws Exception {
        KeYEnvironment<DefaultUserInterfaceControl> env = loadAndRun(keyName);
        try {
            if (!env.getLoadedProof().closed()) {
                System.out.println("--- open goals of " + keyName + " ---");
                for (Goal goal : env.getLoadedProof().openGoals()) {
                    System.out.println(goal.sequent());
                }
            }
            assertThat(env.getLoadedProof().closed()).as("proof of " + keyName + " must close")
                    .isTrue();
        } finally {
            env.dispose();
        }
    }

    /** The proof stays open and the residual carries the given term, pinned as characterization. */
    private void assertProofOpenWith(String keyName, String residualShape) throws Exception {
        KeYEnvironment<DefaultUserInterfaceControl> env = loadAndRun(keyName);
        try {
            assertThat(env.getLoadedProof().closed())
                    .as("residual of " + keyName + " must stay open in auto mode").isFalse();
            String all = String.join("\n", env.getLoadedProof().openGoals().stream()
                    .map(goal -> goal.sequent().toString()).toList());
            assertThat(all).as("open goals of " + keyName + " must carry the residual shape")
                    .contains(residualShape);
            System.out.println("--- open goals of " + keyName + " ---");
            for (Goal goal : env.getLoadedProof().openGoals()) {
                System.out.println(goal.sequent());
            }
        } finally {
            env.dispose();
        }
    }

    private void assertProofOpenAsResidual(String keyName) throws Exception {
        KeYEnvironment<DefaultUserInterfaceControl> env = loadAndRun(keyName);
        try {
            assertThat(env.getLoadedProof().closed())
                    .as("residual of " + keyName + " must stay open (literal in the \\seq)")
                    .isFalse();
            System.out.println("--- open goals of " + keyName + " ---");
            for (Goal goal : env.getLoadedProof().openGoals()) {
                System.out.println(goal.sequent());
            }
        } finally {
            env.dispose();
        }
    }

    private KeYEnvironment<DefaultUserInterfaceControl> loadAndRun(String keyName)
            throws Exception {
        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(
            tmpDir.resolve(keyName));
        assertThat(env.getLoadedProof().getServices().getProfile())
                .isSameAs(JvmProfile.INSTANCE);
        env.getLoadedProof().getSettings().getStrategySettings().setTimeout(300000);
        var macro = new DefaultAutoMacro();
        macro.applyTo(env.getUi(), env.getLoadedProof(), env.getLoadedProof().openGoals(),
            null, env.getUi().getProofControl().getDefaultProverTaskListener());
        return env;
    }

    /** Golden transpiler output + the local runtime, next to the key files. */
    private void setupWorkspace() throws IOException {
        String className = "Category2";
        try (InputStream in = getClass().getResourceAsStream("/golden/" + className + ".java")) {
            Files.copy(in, tmpDir.resolve(className + ".java"));
        }
        Path local = tmpDir.resolve("jvm/Local.java");
        Files.createDirectories(local.getParent());
        try (InputStream in =
            Transpiler.class.getResourceAsStream(Transpiler.LOCAL_RUNTIME_RESOURCE)) {
            Files.copy(in, local);
        }
    }

    private static void writeKeyFile(Path keyFile, String signature) throws IOException {
        String settings = """
                "Choice" : {
                    "JavaCard" : "JavaCard:off",
                    "Strings" : "Strings:on",
                    "assertions" : "assertions:safe",
                    "bigint" : "bigint:on",
                    "floatRules" : "floatRules:strictfpOnly",
                    "initialisation" : "initialisation:disableStaticInitialisation",
                    "intRules" : "intRules:javaSemantics",
                    "integerSimplificationRules" : "integerSimplificationRules:full",
                    "javaLoopTreatment" : "javaLoopTreatment:efficient",
                    "mergeGenerateIsWeakeningGoal" : "mergeGenerateIsWeakeningGoal:off",
                    "methodExpansion" : "methodExpansion:modularOnly",
                    "modelFields" : "modelFields:treatAsAxiom",
                    "moreSeqRules" : "moreSeqRules:off",
                    "permissions" : "permissions:off",
                    "programRules" : "programRules:Java",
                    "reach" : "reach:on",
                    "runtimeExceptions" : "runtimeExceptions:ban",
                    "sequences" : "sequences:on",
                    "wdChecks" : "wdChecks:off",
                    "wdOperator" : "wdOperator:L"
                }
                """;
        String contract =
            "Category2[Category2::%s].JML normal_behavior operation contract.0"
                    .formatted(signature);
        String key = """
                \\profile "java-jvm";

                \\settings {
                %s
                }

                \\javaSource ".";

                \\proofObligation {
                    "class" : "de.uka.ilkd.key.proof.init.FunctionalOperationContractPO",
                    "contract" : "%s",
                    "name" : "%s"
                }

                \\proofScript {
                    macro "script-auto";
                }
                """.formatted(settings, contract, contract);
        Files.writeString(keyFile, key);
    }
}
