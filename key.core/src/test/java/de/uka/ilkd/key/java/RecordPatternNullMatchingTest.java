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
 * Tests the null-matching rules for type patterns inside record patterns (JLS 14.30.1, JLS
 * 14.30.3).
 *
 * <p>
 * A type pattern is null-matching in exactly one situation: it appears directly in the component
 * pattern list of a record pattern and is unconditional for the declared type of the component it
 * lines up with. A pattern is unconditional for a type {@code T} when {@code T} is a subtype of the
 * pattern's type, so every non-null value of {@code T} matches anyway; null-matching extends this
 * to {@code null}. Everywhere else {@code null} does not match a type pattern.
 *
 * <p>
 * The match outcome does not depend on the component's value: an unconditional component pattern
 * imposes no test at all, while a conditional type pattern (for example {@code String s} on an
 * {@code Object} component) tests the component against its type and therefore rejects
 * {@code null}. The shape of the lowering is checked in {@link RecordPatternTest}; the tests here
 * prove the outcome for an unconditional component, for the inferred {@code var} type, and for the
 * top-level pattern.
 */
class RecordPatternNullMatchingTest {

    private static final String A = "public class A { }\n";
    private static final String B = "public class B extends A { }\n";
    private static final String R = "public record R(Object c) { }\n";
    private static final String AB = "public record AB(B value) { }\n";

    @TempDir
    static Path tempDir;

    @BeforeAll
    static void writeSources() throws Exception {
        Path src = tempDir.resolve("src");
        Files.createDirectories(src);
        Files.writeString(src.resolve("A.java"), A);
        Files.writeString(src.resolve("B.java"), B);
        Files.writeString(src.resolve("R.java"), R);
        Files.writeString(src.resolve("AB.java"), AB);
    }

    @Test
    void unconditionalObjectComponentMatchesNull() throws Exception {
        // the component type is Object, the pattern type is Object: unconditional, null-matching
        String program = "R r = new R(null); rb = r instanceof R(Object o);";
        assertProvable(program, "rb = TRUE");
        assertOpen(program, "rb = FALSE");
    }

    @Test
    void unconditionalSupertypeComponentMatchesNull() throws Exception {
        // component type B, pattern type A (a supertype of B): unconditional, null-matching
        String program = "AB r = new AB(null); rb = r instanceof AB(A a);";
        assertProvable(program, "rb = TRUE");
        assertOpen(program, "rb = FALSE");
    }

    @Test
    void varComponentMatchesNull() throws Exception {
        // 'var' infers the component's declared type (Object) and is unconditional for it
        String program = "R r = new R(null); rb = r instanceof R(var x);";
        assertProvable(program, "rb = TRUE");
        assertOpen(program, "rb = FALSE");
    }

    @Test
    void topLevelTypePatternDoesNotMatchNull() throws Exception {
        // outside a record pattern there is no null-matching, not even for Object
        String program = "Object n = null; rb = n instanceof Object x;";
        assertProvable(program, "rb = FALSE");
        assertOpen(program, "rb = TRUE");
    }

    private void assertProvable(String program, String formula) throws Exception {
        assertTrue(prove(program, formula),
            () -> "Expected the proof to close for:\n" + program + "\nFormula: " + formula);
    }

    private void assertOpen(String program, String formula) throws Exception {
        assertFalse(prove(program, formula),
            () -> "The formula must not be provable:\n" + program + "\nFormula: " + formula);
    }

    private boolean prove(String program, String formula) throws Exception {
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setUseJML(true);
        Path src = tempDir.resolve("src");
        Path key = Files.createTempFile(tempDir, "nullmatching", ".key");
        Files.writeString(key, """
                \\profile "Java Profile";
                \\settings {
                    "Choice" : {
                        "runtimeExceptions" : "runtimeExceptions:allow",
                        "assertions" : "assertions:off",
                        "initialisation" : "initialisation:disableStaticInitialisation"
                    },
                    "Strategy" : {
                        "options" : {
                            "METHOD_OPTIONS_KEY" : "METHOD_EXPAND",
                            "LOOP_OPTIONS_KEY" : "LOOP_SCOPE_EXPAND"
                        }
                    }
                }
                \\javaSource "%s";
                \\programVariables { boolean rb; }
                \\problem {
                    \\<{
                %s
                    }\\> %s
                }
                """.formatted(src, program, formula));

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
