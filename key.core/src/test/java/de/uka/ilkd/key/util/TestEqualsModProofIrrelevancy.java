/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.io.File;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

/**
 * Tests for {@link org.key_project.util.EqualsModProofIrrelevancy}.
 *
 * @author Arne Keller
 */
class TestEqualsModProofIrrelevancy {
    public static final File testCaseDirectory = FindResources.getTestCasesDirectory();

    @Test
    void testJavaProof() throws Exception {
        KeYEnvironment<DefaultUserInterfaceControl> env =
            KeYEnvironment.load(new File(testCaseDirectory,
                "../../../../../key.ui/examples/heap/verifyThis15_1_RelaxedPrefix/relax.proof"));
        Assertions.assertNotNull(env.getLoadedProof());
        Assertions.assertTrue(env.getLoadedProof().closed());
        KeYEnvironment<DefaultUserInterfaceControl> env2 =
            KeYEnvironment.load(new File(testCaseDirectory,
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
                SequentFormula sf1 = node1.sequent().getFormulabyNr(j);
                SequentFormula sf2 = node2.sequent().getFormulabyNr(j);
                Assertions.assertTrue(sf1.equalsModProofIrrelevancy(sf2));
            }
            if (node1.getAppliedRuleApp() != null) {
                Assertions.assertTrue(
                    node1.getAppliedRuleApp().equalsModProofIrrelevancy(node2.getAppliedRuleApp()));
            }
        }
    }
}
