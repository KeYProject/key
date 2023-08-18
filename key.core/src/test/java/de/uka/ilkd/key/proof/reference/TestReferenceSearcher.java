/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.reference;

import java.io.File;
import javax.swing.*;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.GeneralSettings;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class TestReferenceSearcher {
    private static final File testCaseDirectory = FindResources.getTestCasesDirectory();

    @Test
    void testFindsReferenceInSameProof() throws Exception {
        GeneralSettings.noPruningClosed = false;
        // test scenario:
        // 1. Load a proof.
        // 2. Use the reference searcher to search for a matching node,
        // using the same proof as reference and "new" proof.
        // This only verifies that an exactly equivalent branch is found.

        KeYEnvironment<DefaultUserInterfaceControl> env =
            KeYEnvironment.load(new File(testCaseDirectory,
                "../../../../../key.ui/examples/heap/verifyThis15_1_RelaxedPrefix/relax.proof"));
        Proof p = env.getLoadedProof();
        KeYEnvironment<DefaultUserInterfaceControl> env2 =
            KeYEnvironment.load(new File(testCaseDirectory,
                "../../../../../key.ui/examples/heap/verifyThis15_1_RelaxedPrefix/relax.proof"));
        Proof p2 = env2.getLoadedProof();

        DefaultListModel<Proof> previousProofs = new DefaultListModel<>();
        previousProofs.addElement(p2);
        DefaultListModel<Proof> newProof = new DefaultListModel<>();
        newProof.addElement(p);

        Node foundReference = null;
        ClosedBy close = null;

        // close by reference only works if there are no branching steps left
        // -> only check the first node in each closed branch
        for (Goal g : p.closedGoals()) {
            Node n = g.node();
            while (n.parent().childrenCount() == 1) {
                n = n.parent();
            }
            if (ReferenceSearcher.suitableForCloseByReference(n)) {
                ClosedBy c = ReferenceSearcher.findPreviousProof(previousProofs, n);
                assertEquals(n.serialNr(), c.getNode().serialNr());
                close = c;
                foundReference = n;
            } else {
                // verify that incompatible nodes return null
                assertNull(ReferenceSearcher.findPreviousProof(previousProofs, n));
            }
            // verify that the reference searcher ignores the current proof
            assertNull(ReferenceSearcher.findPreviousProof(newProof, n));
            // verify that no match can be found
            assertNull(ReferenceSearcher.findPreviousProof(new DefaultListModel<>(), n));
        }

        // test that copying works
        foundReference.register(close, ClosedBy.class);
        p.pruneProof(foundReference);
        p.closeGoal(p.getOpenGoal(foundReference));
        assertTrue(p.closed());
        foundReference.proof().copyCachedGoals(p2, null, null);
        assertTrue(p.closed());

        GeneralSettings.noPruningClosed = true;
        p.dispose();
        p2.dispose();
    }

    @Test
    void checksUserLemmas() throws Exception {
        GeneralSettings.noPruningClosed = false;
        // Test scenario:
        // Proof 1 uses a user-defined lemma.
        // Proof 2 does not.
        // Reference searcher should not find proof 1 when considering proof 2.

        KeYEnvironment<DefaultUserInterfaceControl> env =
            KeYEnvironment.load(new File(testCaseDirectory,
                "proofCaching/proofWithRule.proof"));
        Proof p = env.getLoadedProof();
        KeYEnvironment<DefaultUserInterfaceControl> env2 =
            KeYEnvironment.load(new File(testCaseDirectory,
                "proofCaching/proofWithoutRule.proof"));
        Proof p2 = env2.getLoadedProof();
        KeYEnvironment<DefaultUserInterfaceControl> env3 =
            KeYEnvironment.load(new File(testCaseDirectory,
                "proofCaching/proofWithRule.proof"));
        Proof p3 = env3.getLoadedProof();

        DefaultListModel<Proof> previousProofs = new DefaultListModel<>();
        previousProofs.addElement(p);
        DefaultListModel<Proof> newProof = new DefaultListModel<>();
        newProof.addElement(p2);

        p2.pruneProof(p2.root());

        assertTrue(ReferenceSearcher.suitableForCloseByReference(p2.root()));
        ClosedBy c = ReferenceSearcher.findPreviousProof(previousProofs, p2.root());
        assertNull(c);

        // check that result is found if the user taclet is available
        p3.pruneProof(p3.root());
        assertTrue(ReferenceSearcher.suitableForCloseByReference(p3.root()));
        c = ReferenceSearcher.findPreviousProof(previousProofs, p3.root());
        assertNotNull(c);
        assertEquals(0, c.getNode().serialNr());
        assertEquals(p, c.getProof());

        GeneralSettings.noPruningClosed = true;
        p.dispose();
        p2.dispose();
        p3.dispose();
    }
}
