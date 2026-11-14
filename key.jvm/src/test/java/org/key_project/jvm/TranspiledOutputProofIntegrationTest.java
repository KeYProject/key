/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.jvm;

import java.io.ByteArrayOutputStream;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import javax.tools.ToolProvider;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.macros.DefaultAutoMacro;
import de.uka.ilkd.key.proof.Goal;

import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * M1 integration gate (item 3): transpiles the real {@code fixtures/Max.java}, re-inlines the
 * original JML specs into the emitted sources, compiles the transpiler output with {@code javac}
 * and then proves {@code max(int,int)} / {@code max2(int,int)} against the <em>transpiled
 * output itself</em> with the {@code java-jvm} profile. This is the closest claim to "the
 * transpiler's own output is provable" that the JVM milestone makes end-to-end.
 * <p>
 * (The {@code golden/} twins used by {@code GotoProofTest} are exactly the shape emitted here,
 * completed with the JML contracts ASM cannot retain; {@link Transpiler#transpile(List, Path,
 * List)} restores them from the source so no hand-written twin is needed for this gate.)
 */
class TranspiledOutputProofIntegrationTest {

    @TempDir
    Path tmpDir;

    @Test
    void transpiledOutputClosesTheMethodContracts() throws Exception {
        Path classes = tmpDir.resolve("classes");
        compileFixture(classes);

        List<Path> emitted = Transpiler.transpile(List.of(classes.resolve("Max.class")),
            tmpDir.resolve("out"),
            List.of(classes.resolve("..").resolve("src").resolve("fixtures").resolve("Max.java")));

        Path maxJava = emitted.stream()
                .filter(p -> p.getFileName().toString().equals("Max.java")).findFirst()
                .orElseThrow(() -> new AssertionError("no Max.java emitted"));
        String src = Files.readString(maxJava, StandardCharsets.UTF_8);

        // spec inlining must have restored the contracts the bytecode cannot carry
        assertThat(src).contains("ensures \\result == (a >= b ? a : b)")
                .contains("jvm.Local stk = new jvm.Local();");

        // the emitted output itself must compile
        var compiler = ToolProvider.getSystemJavaCompiler();
        Assumptions.assumeTrue(compiler != null, "no system javac available");
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        int rc = compiler.run(null, null, err, "-d",
            tmpDir.resolve("roundtrip").toString(), "--release", "17", "-g",
            maxJava.toString(),
            tmpDir.resolve("out").resolve("jvm").resolve("Local.java").toString());
        assertThat(rc).as("transpiled output must compile: %s", err).isZero();

        // and the proof gates must close on the transpiled output
        for (String[] gate : new String[][] { { "max(int,int)", "max" },
            { "max2(int,int)", "max2" } }) {
            String contract = "Max[Max::" + gate[0] + "].JML normal_behavior operation contract.0";
            Path keyFile = writeKeyFile(maxJava.getParent(), contract);
            assertThat(runMacro(keyFile)).as("proof of transpiled Max::%s must close", gate[1])
                    .isTrue();
        }
    }

    // -- helpers ---------------------------------------------------------

    private void compileFixture(Path classes) throws Exception {
        Path src = tmpDir.resolve("src").resolve("fixtures");
        Files.createDirectories(src);
        try (InputStream in = getClass().getResourceAsStream("/fixtures/Max.java")) {
            Files.copy(in, src.resolve("Max.java"));
        }
        Files.createDirectories(classes);
        var compiler = ToolProvider.getSystemJavaCompiler();
        Assumptions.assumeTrue(compiler != null, "no system javac available");
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        int rc = compiler.run(null, null, err, "-d", classes.toString(), "--release", "17", "-g",
            src.resolve("Max.java").toString());
        assertThat(rc).as("fixture must compile: %s", err).isZero();
    }

    private Path writeKeyFile(Path dir, String contract) throws Exception {
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
                """.formatted(settings, contract, contract);
        int i = contract.hashCode();
        Path keyFile = dir.resolve("proof-" + Integer.toHexString(i) + ".key");
        Files.writeString(keyFile, key);
        return keyFile;
    }

    private boolean runMacro(Path keyFile) throws Exception {
        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(keyFile);
        try {
            env.getLoadedProof().getSettings().getStrategySettings().setTimeout(300000);
            var macro = new DefaultAutoMacro();
            macro.applyTo(env.getUi(), env.getLoadedProof(), env.getLoadedProof().openGoals(),
                null, env.getUi().getProofControl().getDefaultProverTaskListener());
            boolean closed = env.getLoadedProof().closed();
            if (!closed) {
                System.out.println("--- open goals for " + keyFile.getFileName() + " ---");
                for (Goal goal : env.getLoadedProof().openGoals()) {
                    System.out.println(goal.sequent());
                }
            }
            return closed;
        } finally {
            env.dispose();
        }
    }
}
