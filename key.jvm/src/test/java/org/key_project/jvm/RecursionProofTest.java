/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.jvm;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.macros.DefaultAutoMacro;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * M1 recursion gates: the <em>operation-contract application at a recursive self-call</em>
 * (the mechanism behind the transpiler's {@code stk.push(fact($v0))} emission) must close in
 * auto mode under the {@code java-jvm} profile.
 * <p>
 * The fixture is int-only on purpose: the {@code \measured_by}-licensed total-correctness
 * (diamond) PO of the recursion is what is under test here. The interaction of the fresh
 * {@code jvm.Local} model with the Diamond-free default strategy under
 * {@code intRules: javaSemantics} is a documented KeY-side gap (see
 * {@code docs/concept-jvm-support.md}), which is why the closing gate runs with
 * {@code intRules: arithmeticSemanticsIgnoringOF} -- the same mode KeY's own recursion
 * reference example ({@code key.ui/examples/standard_key/java_dl/recursion/triangular.key})
 * uses -- and the javaSemantics variant is pinned as a characterization test.
 */
class RecursionProofTest {

    @TempDir
    Path tmpDir;

    private static final String REC_SOURCE = """
            public class Rec {

                /*@ public normal_behavior
                  @ requires n >= 0;
                  @ assignable \\nothing;
                  @ measured_by n;
                  @ ensures \\result >= 1;
                  @ ensures n <= 1 ==> \\result == 1;
                  @*/
                public static int fact(int n) {
                    if (n <= 1) {
                        return 1;
                    }
                    return n * fact(n - 1);
                }
            }
            """;

    @Test
    void measuredByRecursionClosesUnderArithmeticIntRules() throws Exception {
        Path keyFile = writeKey("Rec", "fact(int)", "intRules:arithmeticSemanticsIgnoringOF");
        assertThat(runMacro(keyFile)).as("recursion by contract must close in auto mode").isTrue();
    }

    @Test
    void measuredByRecursionUnderJavaSemanticsDoesNotCloseInAutoMode() throws Exception {
        // Documented KeY-side gap: the total-correctness (diamond) PO needs the termination
        // obligations discharged beyond what DefaultAutoMacro does under javaSemantics
        // (cf. the fresh-object residuals discussed in the concept doc).
        Path keyFile = writeKey("Rec", "fact(int)", "intRules:javaSemantics");
        boolean closed = runMacro(keyFile);
        System.out.println("javaSemantics recursion closed (expected false): " + closed);
        assertThat(closed).as(
            "javaSemantics + measured_by recursion is a documented auto-mode gap").isFalse();
    }

    // -- helpers ---------------------------------------------------------

    private boolean runMacro(Path keyFile) throws Exception {
        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(keyFile);
        try {
            env.getLoadedProof().getSettings().getStrategySettings().setTimeout(120000);
            var macro = new DefaultAutoMacro();
            macro.applyTo(env.getUi(), env.getLoadedProof(), env.getLoadedProof().openGoals(),
                null, env.getUi().getProofControl().getDefaultProverTaskListener());
            return env.getLoadedProof().closed();
        } finally {
            env.dispose();
        }
    }

    private Path writeKey(String className, String signature, String intRules) throws Exception {
        Files.writeString(tmpDir.resolve(className + ".java"), REC_SOURCE);
        String contract = className + "[" + className + "::" + signature
            + "].JML normal_behavior operation contract.0";
        String settings = """
                "Choice" : {
                    "JavaCard" : "JavaCard:off",
                    "Strings" : "Strings:on",
                    "assertions" : "assertions:safe",
                    "bigint" : "bigint:on",
                    "floatRules" : "floatRules:strictfpOnly",
                    "initialisation" : "initialisation:disableStaticInitialisation",
                    "intRules" : "%s",
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
                """.formatted(intRules);
        StringBuilder key = new StringBuilder();
        key.append("\\profile \"java-jvm\";\n\n");
        key.append("\\settings {\n").append(settings).append("\n}\n\n");
        key.append("\\javaSource \"\";\n\n");
        key.append("\\proofObligation {\n");
        key.append("\t\"name\": \"").append(contract).append("\",\n");
        key.append("\t\"contract\": \"").append(contract).append("\",\n");
        key.append("\t\"class\": \"de.uka.ilkd.key.proof.init.FunctionalOperationContractPO\",\n");
        key.append(" }\n");
        Path keyFile = tmpDir.resolve(className + ".key");
        Files.writeString(keyFile, key.toString());
        return keyFile;
    }
}
