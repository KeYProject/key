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
 * Proof tests for switch expressions without patterns: the built-in rule must lower them so that
 * the ordinary calculus can prove their contracts.
 */
class SwitchExpressionTest {

    @BeforeAll
    static void enableJml() {
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setUseJML(true);
    }

    private static Proof prove(Path source) throws Exception {
        KeYEnvironment<?> environment = KeYEnvironment.load(source);
        try {
            var contract = environment.getProofContracts().getFirst();
            Proof proof =
                environment.createProof(contract.createProofObl(environment.getInitConfig()));
            ProofStarter starter = new ProofStarter(false);
            starter.init(proof);
            starter.start();
            return proof;
        } finally {
            environment.dispose();
        }
    }

    private static void assertCloses(Path dir, String className, String body) throws Exception {
        Path source = dir.resolve(className + ".java");
        Files.writeString(source, body);
        Proof proof = prove(source);

        assertThat(proof.closed())
                .as("proof did not close, open goals: %s", proof.openGoals())
                .isTrue();
    }



    @Test
    void labeledBreakBaseline(@TempDir Path dir) throws Exception {
        assertCloses(dir, "C", """
                public class C {
                    /*@ normal_behavior
                      @ requires x == 1;
                      @ ensures \\result == 10;
                      @*/
                    int f(int x) {
                        int r;
                        _l: {
                            if (x == 1) { r = 10; break _l; } else { r = 0; break _l; }
                        }
                        return r;
                    }
                }
                """);
    }

    @Test
    void tempComparisonBaseline(@TempDir Path dir) throws Exception {
        assertCloses(dir, "C", """
                public class C {
                    /*@ normal_behavior
                      @ requires x == 1;
                      @ ensures \\result == 10;
                      @*/
                    int f(int x) {
                        int t; t = x;
                        int r;
                        _l: {
                            if (t == 1) { r = 10; break _l; } else { r = 0; break _l; }
                        }
                        return r;
                    }
                }
                """);
    }

    @Test
    void armLabelBaseline(@TempDir Path dir) throws Exception {
        assertCloses(dir, "C", """
                public class C {
                    /*@ normal_behavior
                      @ requires x == 1;
                      @ ensures \\result == 10;
                      @*/
                    int f(int x) {
                        int _sw;
                        if (x == 1) {
                            _c: { _sw = 10; break _c; }
                        } else {
                            _e: { _sw = 0; break _e; }
                        }
                        int i = _sw;
                        return i;
                    }
                }
                """);
    }

    @Test
    void plainIfBaseline(@TempDir Path dir) throws Exception {
        assertCloses(dir, "C", """
                public class C {
                    /*@ normal_behavior
                      @ requires x == 1;
                      @ ensures \\result == 10;
                      @*/
                    int f(int x) {
                        if (x == 1) { return 10; } else { return 0; }
                    }
                }
                """);
    }

    @Test
    void staticReturnSwitchExpression(@TempDir Path dir) throws Exception {
        assertCloses(dir, "C", """
                public class C {
                    /*@ normal_behavior
                      @ requires x == 1;
                      @ ensures \\result == 10;
                      @*/
                    static int f(int x) {
                        return switch (x) { case 1 -> 10; default -> 0; };
                    }
                }
                """);
    }

    @Test
    void constantSelector(@TempDir Path dir) throws Exception {
        assertCloses(dir, "C", """
                public class C {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures \\result == 10;
                      @*/
                    int f() {
                        return switch (0) { case 0 -> 10; default -> 0; };
                    }
                }
                """);
    }

    @Test
    void classicSwitchStatement(@TempDir Path dir) throws Exception {
        assertCloses(dir, "C", """
                public class C {
                    /*@ normal_behavior
                      @ requires x == 1;
                      @ ensures \\result == 10;
                      @*/
                    int f(int x) {
                        switch (x) { case 1: return 10; default: return 0; }
                    }
                }
                """);
    }

    @Test
    void returnSwitchExpression(@TempDir Path dir) throws Exception {
        assertCloses(dir, "C", """
                public class C {
                    /*@ normal_behavior
                      @ requires x == 1;
                      @ ensures \\result == 10;
                      @*/
                    int f(int x) {
                        return switch (x) { case 1 -> 10; default -> 0; };
                    }
                }
                """);
    }

    @Test
    void localVariableInitializer(@TempDir Path dir) throws Exception {
        assertCloses(dir, "C", """
                public class C {
                    /*@ normal_behavior
                      @ requires x == 1;
                      @ ensures \\result == 10;
                      @*/
                    int f(int x) {
                        int r = switch (x) { case 1, 2 -> 10; default -> 0; };
                        return r;
                    }
                }
                """);
    }

    @Test
    void throwArm(@TempDir Path dir) throws Exception {
        assertCloses(dir, "C", """
                public class C {
                    /*@ normal_behavior
                      @ requires x == 1;
                      @ ensures \\result == 10;
                      @*/
                    int f(int x) {
                        return switch (x) {
                            case 1 -> 10;
                            default -> throw new IllegalArgumentException();
                        };
                    }
                }
                """);
    }

    @Test
    void selectorEvaluatedOnce(@TempDir Path dir) throws Exception {
        assertCloses(dir, "C", """
                public class C {
                    static int calls;
                    static int next() { calls++; return 1; }

                    /*@ normal_behavior
                      @ requires true;
                      @ ensures calls == \\old(calls) + 1;
                      @ ensures \\result == 10;
                      @*/
                    int f() {
                        return switch (next()) { case 1 -> 10; default -> 0; };
                    }
                }
                """);
    }

    @Test
    void nestedSwitchExpression(@TempDir Path dir) throws Exception {
        assertCloses(dir, "C", """
                public class C {
                    /*@ normal_behavior
                      @ requires a == 1;
                      @ ensures \\result == 2;
                      @*/
                    int f(int a, int b) {
                        return switch (a) {
                            case 1 -> switch (b) { default -> 2; };
                            default -> 0;
                        };
                    }
                }
                """);
    }

    @Test
    void caseNullArm(@TempDir Path dir) throws Exception {
        assertCloses(dir, "C", """
                public class C {
                    /*@ normal_behavior
                      @ requires s == null;
                      @ ensures \\result == -1;
                      @*/
                    int f(String s) {
                        return switch (s) { case null -> -1; default -> 0; };
                    }
                }
                """);
    }

    @Test
    void unsupportedPositionKeepsTheProofOpen(@TempDir Path dir) throws Exception {
        Path source = dir.resolve("C.java");
        Files.writeString(source, """
                public class C {
                    int h(int x) { return x; }
                    int g(int x, int y) { return x + y; }

                    /*@ normal_behavior
                      @ requires y == 1;
                      @ ensures \\result == 2;
                      @*/
                    int f(int x, int y) {
                        return g(h(x), switch (y) { case 1 -> 1; default -> 0; });
                    }
                }
                """);
        Proof proof = prove(source);
        assertThat(proof.closed()).isFalse();
    }

    @Disabled("blocked on the jmlparser RAW-yield prerequisite (external repository)")
    @Test
    void colonArmWithYield(@TempDir Path dir) throws Exception {
        assertCloses(dir, "C", """
                public class C {
                    /*@ normal_behavior
                      @ requires x == 1;
                      @ ensures \\result == 10;
                      @*/
                    int f(int x) {
                        return switch (x) { case 1: yield 10; default: yield 0; };
                    }
                }
                """);
    }

    @Disabled("blocked on the jmlparser RAW-yield prerequisite (external repository)")
    @Test
    void yieldInsideLoop(@TempDir Path dir) throws Exception {
        assertCloses(dir, "C",
            """
                    public class C {
                        /*@ normal_behavior
                          @ requires x == 1;
                          @ ensures \\result == 7;
                          @*/
                        int f(int x) {
                            return switch (x) {
                                case 1 -> { for (int i = 0; i < 2; i++) { if (i == 1) { yield 7; } } yield 1; }
                                default -> 0;
                            };
                        }
                    }
                    """);
    }
}
