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

import org.key_project.jvm.Transpiler;
import org.key_project.jvm.profile.JvmProfile;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * M2 characterization of the object slice ({@code golden/Point.java} + {@code golden/Shapes.java}
 * + the {@code jvm.Local} runtime). The transpilation side of these fixtures is checked by
 * {@code TranspileTest#transpiledObjectCodeHasCanonicalLayoutAndCompiles}; what is pinned here is
 * the <em>proof</em> side.
 * <p>
 * Unlike the M1 {@code max}/{@code max2} gates, no object-slice method contract closes under
 * {@code DefaultAutoMacro} today: the moment the operand stack carries an <em>Object-typed</em>
 * value (any {@code push(Object)} / {@code popRef()} / {@code topRef()}), the fresh-{@code
 * jvm.Local} createdness residuals of §9.1 (2) surface as succedent goals of the shape
 * {@code created(heap, self_0)}, {@code self_0 != null} in the initial pre-heap. Int-only flows
 * (all of M1) provably avoid them; the whole object slice cannot. Switching to
 * {@code intRules: arithmeticSemanticsIgnoringOF} does not help — the residuals are heap facts,
 * not arithmetic ({@code GotoProofTest#factRecursiveContractGoalShape} documents the same gap for
 * the transpiled recursion).
 * <p>
 * This test pins the current shape precisely (open goals = fresh-object {@code #created}
 * residuals originating in {@code jvm.Local}'s constructor contract), so a KeY-side fix or a
 * proof script in the vein of {@code triangular.proof} is written deliberately instead of
 * silently changing what this suite asserts.
 */
class ObjectProofTest {

    @TempDir
    Path tmpDir;

    @Test
    void objectSliceLeavesFreshObjectCreatednessResidualsOpenInAutoMode() throws Exception {
        setupWorkspace();

        Path keyFile = tmpDir.resolve("proof-make.key");
        writeKeyFile(keyFile);

        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(keyFile);
        try {
            assertThat(env.getLoadedProof().getServices().getProfile())
                    .isSameAs(JvmProfile.INSTANCE);
            env.getLoadedProof().getSettings().getStrategySettings().setTimeout(120000);

            var macro = new DefaultAutoMacro();
            macro.applyTo(env.getUi(), env.getLoadedProof(), env.getLoadedProof().openGoals(),
                null, env.getUi().getProofControl().getDefaultProverTaskListener());

            var open = env.getLoadedProof().openGoals();
            assertThat(open).as(
                "documented gap: Shapes::make must not close in auto mode (Object-typed stack ops)")
                    .isNotEmpty();
            for (var goal : open) {
                String s = goal.sequent().toString();
                // fresh-frame createdness residual of the Local constructor contract's free post,
                // origin-annotated by the Local ctor ensures (see docs/concept-jvm-support.md §9.1)
                assertThat(s).contains("java.lang.Object::#$created");
            }
        } finally {
            env.dispose();
        }
    }

    /** Golden transpiler output (both classes) + the local runtime, next to the key file. */
    private void setupWorkspace() throws IOException {
        for (String className : new String[] { "Point", "Shapes" }) {
            try (InputStream in =
                getClass().getResourceAsStream("/golden/" + className + ".java")) {
                Files.copy(in, tmpDir.resolve(className + ".java"));
            }
        }
        Path local = tmpDir.resolve("jvm/Local.java");
        Files.createDirectories(local.getParent());
        try (InputStream in =
            Transpiler.class.getResourceAsStream(Transpiler.LOCAL_RUNTIME_RESOURCE)) {
            Files.copy(in, local);
        }
    }

    private static void writeKeyFile(Path keyFile) throws IOException {
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
            "Shapes[Shapes::make()].JML normal_behavior operation contract.0";
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
