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

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import static org.junit.jupiter.api.Assertions.assertTrue;

/// Tests record patterns end to end: the guard is evaluated, the components are declared where the
/// pattern is definitely matched, and the proof closes.
class RecordPatternFlowScopingTest {

    @org.junit.jupiter.api.BeforeEach
    void enableJml() {
        // keep the proof independent of test ordering: another test may have disabled JML
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setUseJML(true);
    }

    private static void prove(Path source) throws Exception {
        KeYEnvironment<?> environment = KeYEnvironment.load(source);
        try {
            var contract = environment.getProofContracts().getFirst();
            Proof proof =
                environment.createProof(contract.createProofObl(environment.getInitConfig()));
            ProofStarter starter = new ProofStarter(false);
            starter.setMaxRuleApplications(50_000);
            starter.init(proof);
            starter.start();

            assertTrue(proof.closed(),
                () -> "Proof did not close. Open goals: " + proof.openGoals());
        } finally {
            environment.dispose();
        }
    }

    @Test
    void patternVariablesAreInScopeAfterAbortingThenBranch(@TempDir Path tempDir)
            throws Exception {
        Path source = tempDir.resolve("RecFlowScoping.java");
        Files.writeString(source, """
                public class RecFlowScoping {
                    record Point(int x, int y) { }

                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static boolean m(Object o) {
                        if (!(o instanceof Point(int x, int y))) {
                            return false;
                        }
                        return x >= 0 && y >= 0;
                    }
                }
                """);
        prove(source);
    }

    @Test
    void compoundAndAssignmentUsesBindings(@TempDir Path tempDir) throws Exception {
        Path source = tempDir.resolve("CompoundAndAssignment.java");
        Files.writeString(source, """
                public class CompoundAndAssignment {
                    record Point(int x, int y) { }

                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static boolean m(Object o) {
                        boolean b;
                        b = o instanceof Point(int x, int y) && x > 0;
                        return b;
                    }
                }
                """);
        prove(source);
    }

    @Test
    void compoundOrAssignmentUsesBindings(@TempDir Path tempDir) throws Exception {
        Path source = tempDir.resolve("CompoundOrAssignment.java");
        Files.writeString(source, """
                public class CompoundOrAssignment {
                    record Point(int x, int y) { }

                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static boolean m(Object o) {
                        boolean b;
                        b = !(o instanceof Point(int x, int y)) || x > 0;
                        return b;
                    }
                }
                """);
        prove(source);
    }

    @Test
    void conditionalAssignmentUsesBindings(@TempDir Path tempDir) throws Exception {
        Path source = tempDir.resolve("ConditionalAssignment.java");
        Files.writeString(source, """
                public class ConditionalAssignment {
                    record Point(int x, int y) { }

                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static int m(Object o) {
                        int r;
                        r = o instanceof Point(int x, int y) ? x + y : 0;
                        return r;
                    }
                }
                """);
        prove(source);
    }

    @Test
    void conditionalComponentIsTested(@TempDir Path tempDir) throws Exception {
        Path source = tempDir.resolve("ConditionalComponent.java");
        Files.writeString(source, """
                public class ConditionalComponent {
                    record Box(Object value) { }

                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static int m(Object o) {
                        if (o instanceof Box(String s)) {
                            return s.length();
                        }
                        return 0;
                    }
                }
                """);
        prove(source);
    }
}
