/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.nio.file.Path;
import java.util.Objects;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.EqualityModuloProofIrrelevancy;

import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

/**
 * Tests for equality modulo proof irrelevancy.
 *
 * @author Arne Keller
 */
class TestEqualsModProofIrrelevancy {
    public static final Path testCaseDirectory =
        Objects.requireNonNull(FindResources.getTestCasesDirectory());

    @Test
    void testJavaProof() throws Exception {
        KeYEnvironment<DefaultUserInterfaceControl> env =
            KeYEnvironment.load(testCaseDirectory.resolve(
                "../../../../../key.ui/examples/heap/verifyThis15_1_RelaxedPrefix/relax.proof"));
        Assertions.assertNotNull(env.getLoadedProof());
        Assertions.assertTrue(env.getLoadedProof().closed());
        KeYEnvironment<DefaultUserInterfaceControl> env2 =
            KeYEnvironment.load(testCaseDirectory.resolve(
                "../../../../../key.ui/examples/heap/verifyThis15_1_RelaxedPrefix/relax.proof"));
        Assertions.assertNotNull(env2.getLoadedProof());
        Assertions.assertTrue(env2.getLoadedProof().closed());

        Proof proof1 = env.getLoadedProof();
        Proof proof2 = env.getLoadedProof();

        // compare some proof nodes
        for (int i = 0; i < proof1.countNodes(); i += 15) {
            int serialNr = i;
            Node node1 = proof1.findAny(n -> n.serialNr() == serialNr);
            Node node2 = proof2.findAny(n -> n.serialNr() == serialNr);
            Assertions.assertNotNull(node1);
            Assertions.assertNotNull(node2);
            for (int j = 1; j <= node1.sequent().size(); j++) {
                Sequent sequentFormulas1 = node1.sequent();
                SequentFormula sf1 =
                    sequentFormulas1.getFormulaByNr(j);
                Sequent sequentFormulas = node2.sequent();
                SequentFormula sf2 =
                    sequentFormulas.getFormulaByNr(j);
                Assertions.assertTrue((Object) sf2 instanceof SequentFormula that
                        && EqualityModuloProofIrrelevancy.equalsModProofIrrelevancy(sf1, that));
            }
            if (node1.getAppliedRuleApp() != null) {
                Assertions.assertTrue(
                    EqualityModuloProofIrrelevancy.equalsModProofIrrelevancy(
                        node1.getAppliedRuleApp(), node2.getAppliedRuleApp()));
            }
        }
        env.dispose();
        env2.dispose();
    }
}
