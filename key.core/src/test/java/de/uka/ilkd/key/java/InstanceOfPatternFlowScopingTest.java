/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.ProofStarter;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import static org.junit.jupiter.api.Assertions.assertTrue;

/// Tests the JLS 6.3.1.5 flow scoping of pattern variables. A pattern variable introduced in an
/// `instanceof` pattern is in scope after an `if` statement if the then branch cannot complete
/// normally.
class InstanceOfPatternFlowScopingTest {

    @Test
    void patternVariableIsInScopeAfterAbortingThenBranch(@TempDir Path tempDir) throws Exception {
        Path source = tempDir.resolve("FlowScoping.java");
        Files.writeString(source, """
                public class FlowScoping {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static boolean m(Object o) {
                        if (!(o instanceof String s)) {
                            return false;
                        }
                        return s.isEmpty();
                    }
                }
                """);

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
}
