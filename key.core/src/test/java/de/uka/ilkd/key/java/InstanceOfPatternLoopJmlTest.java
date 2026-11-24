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

/// Tests JML visibility of pattern variables inside and after loop bodies.
class InstanceOfPatternLoopJmlTest {

    private void prove(Path tempDir, String className, String source) throws Exception {
        Path file = tempDir.resolve(className + ".java");
        Files.writeString(file, source);
        KeYEnvironment<?> environment = KeYEnvironment.load(file);
        try {
            var contract = environment.getProofContracts().getFirst();
            Proof proof =
                environment.createProof(contract.createProofObl(environment.getInitConfig()));
            var props = proof.getSettings().getStrategySettings().getActiveStrategyProperties();
            props.setProperty(StrategyProperties.LOOP_OPTIONS_KEY,
                StrategyProperties.LOOP_SCOPE_EXPAND);
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
    void assertInsideWhileBody(@TempDir Path tempDir) throws Exception {
        prove(tempDir, "WhileJmlBody", """
                public class WhileJmlBody {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static void m(Object o) {
                        while (o instanceof String s) {
                            //@ assert s != null;
                            o = null;
                        }
                    }
                }
                """);
    }

    @Test
    void assertAfterWhile(@TempDir Path tempDir) throws Exception {
        prove(tempDir, "WhileJmlAfter", """
                public class WhileJmlAfter {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static void m() {
                        Object o = new String("x");
                        while (!(o instanceof String s)) { o = null; }
                        //@ assert s != null;
                    }
                }
                """);
    }

    @Test
    void assertInsideForBody(@TempDir Path tempDir) throws Exception {
        prove(tempDir, "ForJmlBody", """
                public class ForJmlBody {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static void m() {
                        for (Object o = new String("x");
                             o instanceof String s;
                             o = null) {
                            //@ assert s != null;
                        }
                    }
                }
                """);
    }

    @Test
    void assertAfterDo(@TempDir Path tempDir) throws Exception {
        prove(tempDir, "DoJmlAfter", """
                public class DoJmlAfter {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static void m() {
                        Object o = new String("x");
                        do { o = o; } while (!(o instanceof String s));
                        //@ assert s != null;
                    }
                }
                """);
    }

    @Test
    void doWithLoopInvariant(@TempDir Path tempDir) throws Exception {
        prove(tempDir, "DoInvariant", """
                public class DoInvariant {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures \\result >= 0;
                      @*/
                    public static int m() {
                        Object o = new String("x");
                        int n = 0;
                        /*@ loop_invariant n >= 0; @*/
                        do { n = n + 1; o = null; } while (o instanceof String s);
                        return n;
                    }
                }
                """);
    }
}
