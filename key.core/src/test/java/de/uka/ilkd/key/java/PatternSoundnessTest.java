/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.util.ProofStarter;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Soundness regression tests for {@code instanceof} patterns.
 *
 * <p>
 * Each test pairs a program with the formula that holds in Java and the formula that does not. The
 * former must be provable and the latter must stay open. If a pattern binding is reconstructed by
 * re-evaluating an expression, or reads a stale value, the "false" formula becomes provable.
 *
 * <p>
 * The cases are taken from the soundness review of the pattern stack; they cover the subject
 * evaluation, the binding value in boolean combinations, the after-{@code if} scope, the loop
 * guard, {@code continue} with {@code finally}, and record patterns.
 */
class PatternSoundnessTest {

    private static final String SOURCES = """
            public class A {
                public int g;
                public A next;
            }
            """;

    private static final String DEMOS = """
            public class Demos {
                public static Object id(Object o) {
                    return o;
                }
            }
            """;

    private static final String RECORD = "public record R(Object c) { }\n";

    @TempDir
    static Path tempDir;

    @BeforeAll
    static void writeSources() throws Exception {
        Path src = tempDir.resolve("src");
        Files.createDirectories(src);
        Files.writeString(src.resolve("A.java"), SOURCES);
        Files.writeString(src.resolve("Demos.java"), DEMOS);
        Files.writeString(src.resolve("R.java"), RECORD);
    }

    @Test
    void subjectIsEvaluatedOnce() throws Exception {
        String program = """
                Object[] a = new Object[2];
                a[0] = new A();
                a[1] = new A();
                int i = 0;
                if (a[i++] instanceof A x) { }
                obs = i;
                """;
        // the correct value is covered by the InstanceOfPattern examples; the soundness
        // property tested here is that the wrong value must not be provable
        assertOpen(program, "obs != 1", true);
    }

    @Test
    void bindingUsesTheMatchedValue() throws Exception {
        String program = """
                Object o = new A();
                rb = false;
                if (o instanceof A x && (o = null) == null) {
                    rb = (x == null);
                }
                """;
        assertProvable(program, "rb = FALSE", true);
        assertOpen(program, "rb = TRUE", true);
    }

    @Test
    void spuriousClassCastAfterRightOperand() throws Exception {
        String program = """
                Object o = new A();
                if (o instanceof A x && (o = new Object()) != null) { }
                """;
        assertProvable(program, "true", true);
        assertOpen(program, "false", true);
    }

    @Test
    void doContinueCompletesNormally() throws Exception {
        String program = """
                Object o = new Object();
                if (!(o instanceof A x)) {
                    do { continue; } while (false);
                }
                """;
        assertProvable(program, "true", true);
        assertOpen(program, "false", true);
    }

    @Test
    void assertFalseCompletesNormallyWhenAssertionsAreOff() throws Exception {
        String program = """
                Object o = new Object();
                if (!(o instanceof A x)) {
                    assert false;
                }
                """;
        assertProvable(program, "true", false);
        assertOpen(program, "false", false);
    }

    @Test
    void continueRunsFinallyBeforeTheLoopGuard() throws Exception {
        String program = """
                Object o = new A();
                obs = 0;
                while (Demos.id(o) instanceof A x) {
                    obs = obs + 1;
                    try { continue; } finally { o = null; }
                }
                """;
        assertProvable(program, "obs = 1", true);
        assertOpen(program, "obs != 1", true);
    }

    @Test
    void recordSubjectIsEvaluatedOnce() throws Exception {
        String program = """
                R r = new R(new A());
                Object[] a = new Object[2];
                a[0] = r;
                a[1] = r;
                int i = 0;
                if (a[i++] instanceof R(A x)) { }
                obs = i;
                """;
        assertOpen(program, "obs != 1", true);
    }

    private void assertProvable(String program, String formula, boolean assertions)
            throws Exception {
        assertTrue(prove(program, formula, assertions),
            () -> "Expected the proof to close for:\n" + program + "\nFormula: " + formula);
    }

    private void assertOpen(String program, String formula, boolean assertions) throws Exception {
        assertFalse(prove(program, formula, assertions),
            () -> "The formula must not be provable:\n" + program + "\nFormula: " + formula);
    }

    private boolean prove(String program, String formula, boolean assertions) throws Exception {
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setUseJML(true);
        Path dir = Files.createTempDirectory(tempDir, "case");
        Path src = dir.resolve("src");
        Files.createDirectories(src);
        Files.writeString(src.resolve("A.java"), SOURCES);
        Files.writeString(src.resolve("Demos.java"), DEMOS);
        Files.writeString(src.resolve("R.java"), RECORD);
        Path key = dir.resolve("case.key");
        Files.writeString(key, """
                \\profile "Java Profile";
                \\settings {
                    "Choice" : {
                        "runtimeExceptions" : "runtimeExceptions:allow",
                        "assertions" : "assertions:%s"
                    },
                    "Strategy" : {
                        "options" : {
                            "METHOD_OPTIONS_KEY" : "METHOD_EXPAND",
                            "LOOP_OPTIONS_KEY" : "LOOP_SCOPE_EXPAND"
                        }
                    }
                }
                \\javaSource "src";
                \\programVariables { int obs; boolean rb; }
                \\problem {
                    \\<{
                %s
                    }\\> %s
                }
                """.formatted(assertions ? "on" : "off", program, formula));

        KeYEnvironment<?> environment = KeYEnvironment.load(key);
        try {
            Proof proof = environment.getLoadedProof();
            ProofStarter starter = new ProofStarter(false);
            starter.setMaxRuleApplications(50_000);
            starter.init(proof);
            starter.start();
            return proof.closed();
        } finally {
            environment.dispose();
        }
    }
}
