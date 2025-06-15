/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;

import java.nio.file.Path;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

import org.key_project.logic.PosInTerm;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

/**
 * Tests for the unsat core saving infrastructure.
 */
class TestUnsatCore {
    private static final Path testCaseDirectory = FindResources.getTestCasesDirectory();

    @Test
    void testUnsatCore() throws ProblemLoaderException {
        SmtTestUtils.assumeZ3Installed();

        KeYEnvironment<DefaultUserInterfaceControl> env =
            KeYEnvironment.load(testCaseDirectory.resolve("smt/unsatCore.proof"));
        Assertions.assertNotNull(env.getLoadedProof());
        Assertions.assertTrue(env.getLoadedProof().closed());
        // find the SMT rule app
        Proof p = env.getLoadedProof();
        Node n = p.findAny(node -> node.getAppliedRuleApp() instanceof SMTRuleApp);
        SMTRuleApp app = ((SMTRuleApp) n.getAppliedRuleApp());
        Assertions.assertEquals("Z3", app.getSuccessfulSolverName());
        ImmutableList<PosInOccurrence> ifs = app.assumesInsts();
        Assertions.assertTrue(
            ifs.contains(PosInOccurrence.findInSequent(n.sequent(), 1,
                PosInTerm.getTopLevel())));
        Assertions.assertTrue(
            ifs.contains(PosInOccurrence.findInSequent(n.sequent(), 2,
                PosInTerm.getTopLevel())));
        Assertions.assertTrue(
            ifs.contains(PosInOccurrence.findInSequent(n.sequent(), 3,
                PosInTerm.getTopLevel())));
        Assertions.assertTrue(
            ifs.contains(PosInOccurrence.findInSequent(n.sequent(), 7, PosInTerm.getTopLevel())));
        Assertions.assertEquals(4, ifs.size());
    }

}
