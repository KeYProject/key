package de.uka.ilkd.key.proof.reference;

import java.io.File;
import javax.swing.*;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.replay.CopyingProofReplayer;
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
        assertFalse(p.closed());
        foundReference.proof().copyCachedGoals(p2, null, null);
        assertTrue(p.closed());

        GeneralSettings.noPruningClosed = true;
        p.dispose();
        p2.dispose();
    }
}
