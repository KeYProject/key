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
 * M3 switch slice — proof-side characterization pin. Runs the {@code java-jvm} profile against
 * the transpiled shape of {@code golden/SwitchClass.java}: both methods dispatch on the selector
 * as an if-chain followed by an unconditional default goto, the case/default bodies being guarded
 * {@code L<pc>} blocks with mid-layout or trailing returns (asserted to be byte-exact by
 * {@code TranspileTest#transpiledSwitchHasCanonicalShape}).
 * <p>
 * These <em>do not close</em> under {@code DefaultAutoMacro} — not because of the goto/label
 * plumbing (variable-only flows with the same machinery close; cf. {@code GotoProofTest}) but
 * because the switch flow necessarily carries <em>constants</em>: branch tests against literal
 * keys and literal pushes into {@code jvm.Local}. A probe bisect
 * ({@code ProbeSwitchBisectTest}, deleted after use) pinned the boundary: any constant in the
 * stack flow leaves the fresh-{@code jvm.Local} obligations of the constructor contract open as
 * {@code ¬(branch condition) ∨ created(heap,self) ∨ self=null ∨ inRangeInt(literal)} succedent
 * disjuncts, exactly the §9.1(2) residual family. This test pins that behaviour, so a KeY-side
 * strategy fix (the {@code selectCreatedOfAnon} cost band, §9.1(2)) is written deliberately.
 */
class SwitchProofTest {

    @TempDir
    Path tmpDir;

    @Test
    void tableswitchClassifyResidualShape() throws Exception {
        assertResidualShape("SwitchClass", "classify(int)");
    }

    @Test
    void lookupswitchLookupResidualShape() throws Exception {
        assertResidualShape("SwitchClass", "lookup(int)");
    }

    private void assertResidualShape(String className, String signature) throws Exception {
        setupWorkspace(className);

        Path keyFile = tmpDir.resolve("proof.key");
        writeKeyFile(keyFile, className, signature);

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
                "documented gap: constant-typed switch flows must not close in auto mode")
                    .isNotEmpty();
            for (Goal goal : open) {
                String s = goal.sequent().toString();
                // the fresh-Local residual of the Local constructor contract (createdness in
                // the pre-heap vs. self==null) plus the trivial-but-unreduced literal range
                // obligations of the constant stack flow
                assertThat(s).contains("jvm.Local::#contents")
                        .contains("ensures @ file Local.java")
                        .contains("#$created");
            }
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
