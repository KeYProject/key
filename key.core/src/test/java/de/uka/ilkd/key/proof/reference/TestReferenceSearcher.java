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

        DefaultListModel<Proof> previousProofs = new DefaultListModel<>();
        previousProofs.addElement(p);

        // close by reference only works if there are no branching steps left
        // -> only check the first node in each closed branch
        for (Goal g : p.closedGoals()) {
            Node n = g.node();
            while (n.parent().childrenCount() == 1) {
                n = n.parent();
            }
            if (ReferenceSearcher.suitableForCloseByReference(n)) {
                ClosedBy c = ReferenceSearcher.findPreviousProof(previousProofs, n);
                assertEquals(n, c.getNode());
            }
        }
        GeneralSettings.noPruningClosed = true;
    }
}
