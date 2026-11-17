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
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.ProofStarter;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import static org.junit.jupiter.api.Assertions.assertTrue;

/// Tests the JLS 6.3.1.5 flow scoping of pattern variables. A pattern variable introduced in an
/// `instanceof` pattern is in scope after an `if` statement if the then branch cannot complete
/// normally.
class InstanceOfPatternFlowScopingTest {
    @BeforeAll
    static void enableJml() {
        // keep the test independent of test ordering: other tests may have changed the global
        // proof settings (strategy) or disabled JML
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings()
                .setActiveStrategyProperties(new StrategyProperties());
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setUseJML(true);
    }


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
            starter.init(proof);
            starter.start();

            assertTrue(proof.closed(),
                () -> "Proof did not close. Open goals: " + proof.openGoals());
        } finally {
            environment.dispose();
        }
    }

    @Test
    void declarationInitializerUsesTheBinding(@TempDir Path tempDir) throws Exception {
        Path source = tempDir.resolve("DeclarationInitializer.java");
        Files.writeString(source, """
                public class DeclarationInitializer {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static boolean m(Object o) {
                        boolean b = o instanceof String s && s.length() > 0;
                        return b;
                    }
                }
                """);

        KeYEnvironment<?> environment = KeYEnvironment.load(source);
        try {
            var contract = environment.getProofContracts().getFirst();
            Proof proof =
                environment.createProof(contract.createProofObl(environment.getInitConfig()));
            ProofStarter starter = new ProofStarter(false);
            starter.init(proof);
            starter.start();

            assertTrue(proof.closed(),
                () -> "Proof did not close. Open goals: " + proof.openGoals());
        } finally {
            environment.dispose();
        }
    }
}
