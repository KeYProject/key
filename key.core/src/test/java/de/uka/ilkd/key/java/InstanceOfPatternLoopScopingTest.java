/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.ProofStarter;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import static org.junit.jupiter.api.Assertions.assertTrue;

/// Tests JLS 6.3.2.3-6.3.2.5 flow scoping for pattern variables in loops.
class InstanceOfPatternLoopScopingTest {

    private void prove(Path tempDir, String className, String source, String loopOption)
            throws Exception {
        Path file = tempDir.resolve(className + ".java");
        Files.writeString(file, source);
        KeYEnvironment<?> environment = KeYEnvironment.load(file);
        try {
            var contract = environment.getProofContracts().getFirst();
            Proof proof =
                environment.createProof(contract.createProofObl(environment.getInitConfig()));
            var props = proof.getSettings().getStrategySettings().getActiveStrategyProperties();
            props.setProperty(StrategyProperties.LOOP_OPTIONS_KEY, loopOption);
            proof.setActiveStrategy(proof.getActiveStrategyFactory().create(proof, props));
            ProofStarter starter = new ProofStarter(false);
            starter.init(proof);
            starter.start();
            assertTrue(proof.closed(), () -> "Open goals: " + proof.openGoals());
        } finally {
            environment.dispose();
        }
    }

    @Test
    void whileBodyBinding(@TempDir Path tempDir) throws Exception {
        prove(tempDir, "WhileBody", """
                public class WhileBody {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures \\result >= 0;
                      @*/
                    public static int m(Object o) {
                        int n = 0;
                        while (o instanceof String s) {
                            n += s.length();
                            o = null;
                        }
                        return n;
                    }
                }
                """, StrategyProperties.LOOP_SCOPE_EXPAND);
    }

    @Test
    void whileAfterBinding(@TempDir Path tempDir) throws Exception {
        prove(tempDir, "WhileAfter", """
                public class WhileAfter {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures \\result >= 0;
                      @*/
                    public static int m() {
                        Object o = new String("x");
                        while (!(o instanceof String s)) { o = null; }
                        return s.length();
                    }
                }
                """, StrategyProperties.LOOP_SCOPE_EXPAND);
    }

    @Test
    void forBodyAndUpdateBinding(@TempDir Path tempDir) throws Exception {
        prove(tempDir, "ForBody", """
                public class ForBody {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures \\result >= 0;
                      @*/
                    public static int m(Object o) {
                        int n = 0;
                        for (; o instanceof String s; o = null) {
                            n += s.length();
                        }
                        return n;
                    }
                }
                """, StrategyProperties.LOOP_SCOPE_EXPAND);
    }

    @Test
    void doAfterBinding(@TempDir Path tempDir) throws Exception {
        prove(tempDir, "DoAfter", """
                public class DoAfter {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures \\result >= 0;
                      @*/
                    public static int m() {
                        Object o = new String("x");
                        do { o = o; } while (!(o instanceof String s));
                        return s.length();
                    }
                }
                """, StrategyProperties.LOOP_SCOPE_EXPAND);
    }

    @Test
    void nestedBlockBinding(@TempDir Path tempDir) throws Exception {
        prove(tempDir, "NestedBlock", """
                public class NestedBlock {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures \\result >= 0;
                      @*/
                    public static int m(Object o) {
                        int n = 0;
                        if (o != null) {
                            while (o instanceof String s) {
                                n += s.length();
                                o = null;
                            }
                        }
                        return n;
                    }
                }
                """, StrategyProperties.LOOP_SCOPE_EXPAND);
    }
}
