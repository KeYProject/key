/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;

import java.nio.file.Path;
import java.util.Objects;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

import org.key_project.logic.PosInTerm;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for the unsat core saving infrastructure.
 */
class TestUnsatCore {
    private static final Path testCaseDirectory =
        Objects.requireNonNull(FindResources.getTestCasesDirectory());

    @Test
    void testUnsatCore() throws ProblemLoaderException {
        SmtTestUtils.assumeZ3Installed();

        KeYEnvironment<DefaultUserInterfaceControl> env =
            KeYEnvironment.load(testCaseDirectory.resolve("smt/unsatCore.proof"));
        assertNotNull(env.getLoadedProof());
        assertTrue(env.getLoadedProof().closed());
        // find the SMT rule app
        Proof p = env.getLoadedProof();
        Node n = p.findAny(node -> node.getAppliedRuleApp() instanceof SMTRuleApp);
        assertNotNull(n);
        SMTRuleApp app = ((SMTRuleApp) n.getAppliedRuleApp());
        System.out.println(app);
        assertEquals("Z3", app.getSuccessfulSolverName());
        ImmutableList<PosInOccurrence> ifs = app.assumesInsts();
        var pio1 = PosInOccurrence.findInSequent(n.sequent(), 1, PosInTerm.getTopLevel());
        var pio2 = PosInOccurrence.findInSequent(n.sequent(), 2, PosInTerm.getTopLevel());
        var pio3 = PosInOccurrence.findInSequent(n.sequent(), 3, PosInTerm.getTopLevel());
        var pio7 = PosInOccurrence.findInSequent(n.sequent(), 7, PosInTerm.getTopLevel());

        assertEquals(4, ifs.size());
        assertThat(ifs).containsExactlyInAnyOrder(pio1, pio2, pio3, pio7);
    }

}
