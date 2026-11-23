/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.ProofStarter;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * End-to-end proofs for boxing and unboxing in assignment contexts.
 */
class AutoboxingProofTest {

    @BeforeAll
    static void enableJml() {
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings()
                .setActiveStrategyProperties(new StrategyProperties());
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setUseJML(true);
    }

    private static Proof proof(String className, String source, String method, Path dir)
            throws Exception {
        Path sub = Files.createDirectories(dir.resolve(className));
        Path file = sub.resolve(className + ".java");
        Files.writeString(file, source);

        KeYEnvironment<?> env = KeYEnvironment.load(file);
        try {
            var contract = env.getProofContracts().stream()
                    .filter(c -> c.getTarget() instanceof IProgramMethod pm
                            && pm.getMethodDeclaration().getName().equals(method))
                    .findFirst()
                    .orElseThrow(() -> new AssertionError("no contract for " + method));
            Proof proof = env.createProof(contract.createProofObl(env.getInitConfig()));
            ProofStarter starter = new ProofStarter(false);
            starter.init(proof);
            starter.start();
            return proof;
        } finally {
            env.dispose();
        }
    }

    private static void prove(String className, String source, Path dir) throws Exception {
        Proof proof = proof(className, source, "m", dir);
        assertTrue(proof.closed(), () -> "Proof did not close. Open goals: " + proof.openGoals());
    }

    private static String clazz(String className, String body) {
        return """
                public class %s {
                    %s
                }
                """.formatted(className, body);
    }

    @Test
    void localVariable(@TempDir Path dir) throws Exception {
        prove("LocalVariable", clazz("LocalVariable", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Integer a = 42;
                    int i = a;
                    //@ assert i == 42;
                }
                """), dir);
    }

    @Test
    void fieldAssignment(@TempDir Path dir) throws Exception {
        prove("FieldAssignment", clazz("FieldAssignment", """
                Integer f;

                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public void m() {
                    f = 42;
                    int i = f;
                    //@ assert i == 42;
                }
                """), dir);
    }

    @Test
    void returnValue(@TempDir Path dir) throws Exception {
        prove("ReturnValue", clazz("ReturnValue", """
                static Integer box() {
                    return 42;
                }

                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    int i = box();
                    //@ assert i == 42;
                }
                """), dir);
    }

    @Test
    void nullUnboxingSplits(@TempDir Path dir) throws Exception {
        Proof proof = proof("NullUnboxing", clazz("NullUnboxing", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Integer a = null;
                    int i = a;
                }
                """), "m", dir);
        assertFalse(proof.closed(), "null unboxing must not silently verify");
        boolean falseGoal = proof.openGoals().stream().anyMatch(goal -> {
            String label = goal.node().getNodeInfo().getBranchLabel();
            boolean nullLabel = label != null && label.contains("Null");
            return nullLabel || goal.sequent().succedent().isEmpty();
        });
        assertTrue(falseGoal, () -> "expected the null/false branch, got: " + proof.openGoals());
    }
}
