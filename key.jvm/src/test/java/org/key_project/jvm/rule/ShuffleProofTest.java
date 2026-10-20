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
 * M3 stack-shuffle proof gate. {@code golden/Shuffle.java} carries the exact transpiled shape
 * of javac-17's real `dup` bytecode ({@code (x = y) + x} → {@code stk.push(y); stk.dup();
 * x = stk.pop(); ...}) — a <em>variable-only int</em> flow with no constant reaching the
 * {@code \seq}. Per the §9.1(2) bisect boundary, such flows close under
 * {@code DefaultAutoMacro}, so {@code dupReuse} here is the first genuinely closing M3 gate
 * (the switch fixtures are pinned, cf. {@code SwitchProofTest}; the array-based {@code dup2A}
 * twin carries the Object-typed array residual and is deliberately not asserted closed).
 */
class ShuffleProofTest {

    @TempDir
    Path tmpDir;

    @Test
    void dupReuseShuffleProofCloses() throws Exception {
        setupWorkspace("Shuffle");

        Path keyFile = tmpDir.resolve("proof.key");
        writeKeyFile(keyFile, "Shuffle", "dupReuse(int,int)");

        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(keyFile);
        try {
            assertThat(env.getLoadedProof().getServices().getProfile())
                    .isSameAs(JvmProfile.INSTANCE);

            env.getLoadedProof().getSettings().getStrategySettings().setTimeout(300000);
            var macro = new DefaultAutoMacro();
            macro.applyTo(env.getUi(), env.getLoadedProof(), env.getLoadedProof().openGoals(),
                null, env.getUi().getProofControl().getDefaultProverTaskListener());

            if (!env.getLoadedProof().closed()) {
                System.out.println("--- open goals ---");
                for (Goal goal : env.getLoadedProof().openGoals()) {
                    System.out.println(goal.sequent());
                }
            }
            assertThat(env.getLoadedProof().closed())
                    .as("proof of Shuffle::dupReuse must close").isTrue();
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
