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
 * M3 exceptions proof gates on {@code golden/Exceptions.java}, the exact transpiled shape of
 * javac-17's real try/catch bytecode (exceptions slice): the exception table is reconstructed
 * into structured {@code try/catch} blocks, handlers are consumed into catch clauses, and
 * {@code athrow} becomes a real {@code throw} (declared via {@code throws Throwable}).
 * <p>
 * {@code guarded} and {@code finallyFlow} stay open in auto mode on the <em>fresh-Local
 * createdness</em> residual of §9.1(2) — the {@code Local} constructor contract's
 * {@code ==\> created(self), self = null} succedent obligations that the default strategy never
 * reduces (the same family as the switch pins) — at the point right after the {@code local}
 * ctor, before the {@code goto_} of the {@code ifge} leaves the throwing region; their constant
 * stack flow ({@code stk.push(1)}/{@code stk.push(2)}, an Object-typed allocation and a
 * {@code String} literal) belongs to the same residual family. {@code thrower} <em>closes</em>:
 * its {@code requires x >= 0} makes the throwing branch contradictory, so the variable-only
 * normal path (including the {@code LDC} String and the {@code new+<init>} with a String
 * argument on the dead path) proves under {@code DefaultAutoMacro} — the first exceptions-shaped
 * closing gate of the slice. Division ({@code idiv}) and array bounds are avoided in the
 * fixtures on purpose: both are contractless or blocked by {@code runtimeExceptions: ban}.
 */
class ExceptionsProofTest {

    @TempDir
    Path tmpDir;

    /** The catch-bound path pushes constants and an exception allocation, so §9.1(2) holds. */
    @Test
    void guardedTypedCatchLeavesFreshLocalResidual() throws Exception {
        setupWorkspace();
        writeKeyFile(tmpDir.resolve("guarded.key"), "guarded(int)");
        assertProofOpenWithCreatednessResidual("guarded.key");
    }

    /** The finally-inlined catch-all rethrow adds constants and an Object-typed flow. */
    @Test
    void finallyFlowInlineFinallyLeavesFreshLocalResidual() throws Exception {
        setupWorkspace();
        writeKeyFile(tmpDir.resolve("finallyFlow.key"), "finallyFlow(int)");
        assertProofOpenWithCreatednessResidual("finallyFlow.key");
    }

    /**
     * thrower closes: {@code requires x >= 0} refutes the throwing branch, so only the
     * variable-only normal path is proven. The athrow emission, the {@code LDC} String push and
     * the {@code new+<init>} with a String argument all live on the dead (x < 0) path; the
     * createdness residual never appears because that path contradicts the requires.
     */
    @Test
    void throwerUncaughtThrowClosesUnderRequires() throws Exception {
        setupWorkspace();
        writeKeyFile(tmpDir.resolve("thrower.key"), "thrower(int)");
        assertProofCloses("thrower.key");
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

    /**
     * The proof stays open on the §9.1(2) fresh-Local createdness residual: every open goal
     * carries the {@code Local} constructor contract's obligations (its free post
     * {@code contents == \seq_empty && size == 0}, the fresh-create succedent
     * {@code created(self), self = null}) that auto mode never discharges.
     */
    private void assertProofOpenWithCreatednessResidual(String keyName) throws Exception {
        KeYEnvironment<DefaultUserInterfaceControl> env = loadAndRun(keyName);
        try {
            var open = env.getLoadedProof().openGoals();
            assertThat(open).as(
                "documented gap: constant/object-carrying exception flows must not close")
                    .isNotEmpty();
            for (Goal goal : open) {
                String s = goal.sequent().toString();
                assertThat(s).contains("jvm.Local::#contents")
                        .contains("ensures @ file Local.java")
                        .contains("#$created");
            }
            System.out.println("--- open goals of " + keyName + " ---");
            for (Goal goal : open) {
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

    /** Golden transpiler output + the local runtime, next to the key file. */
    private void setupWorkspace() throws IOException {
        try (InputStream in = getClass().getResourceAsStream("/golden/Exceptions.java")) {
            Files.copy(in, tmpDir.resolve("Exceptions.java"));
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
            "Exceptions[Exceptions::%s].JML normal_behavior operation contract.0"
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
