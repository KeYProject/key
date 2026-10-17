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
 * M1 proof gates. Runs the {@code java-jvm} profile against the golden transpiler output
 * ({@code golden/Max.java}, i.e. the exact source shape the transpiler emits for {@code max} /
 * {@code max2}, hand-completed with the JML contracts ASM cannot retain).
 * <p>
 * {@link GotoSpliceRule} resolves the forward {@code goto_(…)} calls, {@link IfLiteralRule}
 * removes the label guards / mid-layout wrappers, and the JML contracts of {@code jvm.Local}
 * formalize every other instruction -- so the method contracts must close automatically.
 * <p>
 * The recursive fixture ({@code golden/Fact.java}) is deliberately <em>not</em> asserted to
 * close here: with the default strategy the fresh-object obligations of the {@code jvm.Local}
 * constructor contract stay open in auto mode (see {@link #factRecursiveContractGoalShape} and
 * the {@code docs/concept-jvm-support.md} "known limitations" section). The recursion itself
 * closes in auto mode under {@code intRules: arithmeticSemanticsIgnoringOF} -- see
 * {@code RecursionProofTest}.
 */
class GotoProofTest {

    @TempDir
    Path tmpDir;

    @Test
    void maxForwardGotoProofCloses() throws Exception {
        assertProofCloses("Max", "max(int,int)");
    }

    @Test
    void max2ForwardGotoWithMidLayoutReturnProofCloses() throws Exception {
        assertProofCloses("Max", "max2(int,int)");
    }

    /**
     * Characterization of a documented KeY-side strategy gap (see the concept doc, "Known
     * limitations"): the transpiled recursive {@code Fact::fact} does not close under
     * {@code DefaultAutoMacro} + {@code intRules: javaSemantics}. The open goals are exactly the
     * "fresh {@code jvm.Local} created in the pre-heap" obligations of the constructor
     * contract's free post -- provable only via the {@code selectCreatedOfAnon} reduction that
     * the default strategy hard-disables ({@code simplify_heap_high_costs} is bound to infinity).
     * <p>
     * This test pins the current behaviour precisely, so that a KeY-side fix (or a proof script
     * in the vein of {@code triangular.proof}) is written deliberately instead of silently
     * changing what this suite asserts.
     */
    @Test
    void factRecursiveContractGoalShape() throws Exception {
        setupWorkspace("Fact");
        Path keyFile = tmpDir.resolve("proof-fact.key");
        writeKeyFile(keyFile, "Fact", "fact(int)");

        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(keyFile);
        try {
            env.getLoadedProof().getSettings().getStrategySettings().setTimeout(120000);
            var macro = new DefaultAutoMacro();
            macro.applyTo(env.getUi(), env.getLoadedProof(), env.getLoadedProof().openGoals(),
                null, env.getUi().getProofControl().getDefaultProverTaskListener());

            var open = env.getLoadedProof().openGoals();
            assertThat(open).as("documented gap: Fact must not close in auto-javaSemantics mode")
                    .isNotEmpty();
            for (Goal goal : open) {
                String s = goal.sequent().toString();
                // residual succedent obligations come from the Local constructor's implicit
                // free post (fresh-object createdness + non-null) against the pre-heap
                assertThat(s).contains("jvm.Local::#contents")
                        .contains("ensures @ file Local.java");
            }
        } finally {
            env.dispose();
        }
    }

    private void assertProofCloses(String className, String signature) throws Exception {
        setupWorkspace(className);

        Path keyFile = tmpDir.resolve("proof.key");
        writeKeyFile(keyFile, className, signature);

        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(keyFile);
        try {
            assertThat(env.getLoadedProof().getServices().getProfile())
                    .isSameAs(JvmProfile.INSTANCE);

            // Bound the strategy time so a broken rule cannot hang the CI.
            env.getLoadedProof().getSettings().getStrategySettings().setTimeout(300000);

            var macro = new DefaultAutoMacro();
            macro.applyTo(env.getUi(), env.getLoadedProof(), env.getLoadedProof().openGoals(),
                null, env.getUi().getProofControl().getDefaultProverTaskListener());

            System.out.println(env.getLoadedProof());
            if (!env.getLoadedProof().closed()) {
                System.out.println("--- open goals ---");
                for (var goal : env.getLoadedProof().openGoals()) {
                    System.out.println(goal.sequent());
                }
            }
            assertThat(env.getLoadedProof().closed())
                    .as("proof of %s::%s must close", className, signature).isTrue();
        } finally {
            env.dispose();
        }
    }

    /** Golden transpiler output + the local runtime, next to the key file. */
    private void setupWorkspace(String className) throws IOException {
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

    private static void writeKeyFile(Path keyFile, String className, String signature)
            throws IOException {
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
            "%s[%s::%s].JML normal_behavior operation contract.0".formatted(className,
                className, signature);
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
