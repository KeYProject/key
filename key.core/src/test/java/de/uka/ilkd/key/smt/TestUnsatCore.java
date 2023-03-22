package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.helper.FindResources;

import java.io.File;

/**
 * Tests for the unsat core saving infrastructure.
 */
class TestUnsatCore {
    public static final File testCaseDirectory = FindResources.getTestCasesDirectory();

    @Test
    void testUnsatCore() throws ProblemLoaderException {
        KeYEnvironment<DefaultUserInterfaceControl> env =
            KeYEnvironment.load(new File(testCaseDirectory, "smt/unsatCore.proof"));
        Assertions.assertNotNull(env.getLoadedProof());
        Assertions.assertTrue(env.getLoadedProof().closed());
        // find the SMT rule app
        Proof p = env.getLoadedProof();
        Node n = p.findAny(node -> node.getAppliedRuleApp() instanceof RuleAppSMT);
        RuleAppSMT app = ((RuleAppSMT) n.getAppliedRuleApp());
        Assertions.assertEquals("Z3", app.getSuccessfulSolverName());
        ImmutableList<PosInOccurrence> ifs = app.ifInsts();
        Assertions.assertTrue(
            ifs.contains(PosInOccurrence.findInSequent(n.sequent(), 1, PosInTerm.getTopLevel())));
        Assertions.assertTrue(
            ifs.contains(PosInOccurrence.findInSequent(n.sequent(), 2, PosInTerm.getTopLevel())));
        Assertions.assertTrue(
            ifs.contains(PosInOccurrence.findInSequent(n.sequent(), 3, PosInTerm.getTopLevel())));
        Assertions.assertTrue(
            ifs.contains(PosInOccurrence.findInSequent(n.sequent(), 7, PosInTerm.getTopLevel())));
        Assertions.assertEquals(4, ifs.size());
    }
}
