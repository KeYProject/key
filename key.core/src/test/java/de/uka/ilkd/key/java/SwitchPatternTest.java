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
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Proof tests for pattern matching in switch statements and switch expressions: type patterns,
 * {@code when} guards and record patterns are lowered to {@code instanceof} guards.
 */
class SwitchPatternTest {

    @BeforeAll
    static void enableJml() {
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setUseJML(true);
    }

    private static void assertCloses(Path dir, String className, String body) throws Exception {
        Path source = dir.resolve(className + ".java");
        Files.writeString(source, body);
        KeYEnvironment<?> environment = KeYEnvironment.load(source);
        try {
            var contract = environment.getProofContracts().getFirst();
            Proof proof =
                environment.createProof(contract.createProofObl(environment.getInitConfig()));
            ProofStarter starter = new ProofStarter(false);
            starter.init(proof);
            starter.start();
            assertThat(proof.closed())
                    .as("proof did not close, open goals: %s", proof.openGoals())
                    .isTrue();
        } finally {
            environment.dispose();
        }
    }

    @Test
    void typePatternStatement(@TempDir Path dir) throws Exception {
        assertCloses(dir, "C", """
                public class C {
                    /*@ normal_behavior
                      @ requires o instanceof Integer;
                      @ ensures \\result == 2;
                      @*/
                    static int f(Object o) {
                        switch (o) {
                            case Integer i: return 1 + 1;
                            default: return -1;
                        }
                    }
                }
                """);
    }

    @Test
    void guardedTypePatternStatement(@TempDir Path dir) throws Exception {
        assertCloses(dir, "C", """
                public class C {
                    /*@ normal_behavior
                      @ requires o instanceof Integer;
                      @ ensures \\result == 1;
                      @*/
                    static int f(Object o) {
                        switch (o) {
                            case Integer i when 1 > 0: return 1;
                            default: return 0;
                        }
                    }
                }
                """);
    }

    @Test
    void stringPatternStatement(@TempDir Path dir) throws Exception {
        assertCloses(dir, "C", """
                public class C {
                    /*@ normal_behavior
                      @ requires o instanceof String;
                      @ ensures \\result == 1;
                      @*/
                    static int f(Object o) {
                        switch (o) {
                            case String s: return 1;
                            default: return 0;
                        }
                    }
                }
                """);
    }

    @Disabled("blocked on the base pattern stack's binding-hint side conditions (see the pattern PR notes)")
    @Test
    void typePatternExpression(@TempDir Path dir) throws Exception {
        assertCloses(dir, "C", """
                public class C {
                    /*@ normal_behavior
                      @ requires o instanceof Integer;
                      @ ensures \\result == 1;
                      @*/
                    static int f(Object o) {
                        return switch (o) { case Integer i -> 1; default -> 0; };
                    }
                }
                """);
    }

    @Disabled("blocked on the base pattern stack's binding-hint side conditions (see the pattern PR notes)")
    @Test
    void recordPatternExpression(@TempDir Path dir) throws Exception {
        assertCloses(dir, "C", """
                public class C {
                    record Point(int x, int y) { }

                    /*@ normal_behavior
                      @ requires o instanceof Point;
                      @ ensures \\result == 1;
                      @*/
                    static int f(Object o) {
                        return switch (o) {
                            case Point(int x, int y) -> 1;
                            default -> 0;
                        };
                    }
                }
                """);
    }

    @Test
    void guardNotEvaluatedWhenPatternDoesNotMatch(@TempDir Path dir) throws Exception {
        assertCloses(dir, "C", """
                public class C {
                    static int ticks;
                    static boolean tick() { ticks++; return true; }

                    /*@ normal_behavior
                      @ requires !(o instanceof Integer);
                      @ ensures ticks == \\old(ticks);
                      @*/
                    static int f(Object o) {
                        switch (o) {
                            case Integer i when tick(): return 1;
                            default: return 0;
                        }
                    }
                }
                """);
    }
}
