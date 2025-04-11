/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

import java.io.File;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTSolverResult;
import de.uka.ilkd.key.smt.SMTTestSettings;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.smt.solvertypes.SolverTypeImplementation;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static org.junit.jupiter.api.Assertions.*;

/**
 * This class is for testing the translation of modulo from KeY to SMT
 *
 * @author Nils Buchholz, 2024
 */
public class TestSMTMod {

    private static final Logger LOGGER = LoggerFactory.getLogger(TestSMTMod.class);

    private static final File testCaseDirectory = FindResources.getTestCasesDirectory();

    private static final SolverType Z3_SOLVER = SolverTypes.getSolverTypes().stream()
            .filter(it -> it.getClass().equals(SolverTypeImplementation.class)
                    && it.getName().equals("Z3"))
            .findFirst().orElse(null);

    private static final SolverType CVC5_SOLVER = SolverTypes.getSolverTypes().stream()
            .filter(it -> it.getClass().equals(SolverTypeImplementation.class)
                    && it.getName().equals("cvc5"))
            .findFirst().orElse(null);

    /**
     * This tests if x mod y is non-negative and x mod y < |y| for y != 0
     * thus satisfying the definition of euclidean modulo
     * Tests for Z3 and cvc5
     *
     * @throws ProblemLoaderException Occured Exception during load of problem file
     */
    @Test
    public void testModSpec() throws ProblemLoaderException {
        KeYEnvironment<DefaultUserInterfaceControl> env =
            KeYEnvironment.load(new File(testCaseDirectory, "smt/modSpec.key"));
        try {
            Proof proof = env.getLoadedProof();
            assertNotNull(proof);
            assertEquals(1, proof.openGoals().size());
            Goal g = proof.openGoals().iterator().next();
            SMTSolverResult result;
            if (Z3_SOLVER.isInstalled(true)) {
                result = checkGoal(g, Z3_SOLVER);
                assertSame(SMTSolverResult.ThreeValuedTruth.VALID, result.isValid());
            } else {
                LOGGER.warn("Warning:Z3 solver not installed, tests skipped.");
            }
            if (CVC5_SOLVER.isInstalled(true)) {
                result = checkGoal(g, CVC5_SOLVER);
                assertSame(SMTSolverResult.ThreeValuedTruth.VALID, result.isValid());
            } else {
                LOGGER.warn("Warning:cvc5 solver not installed, tests skipped.");
            }
        } finally {
            env.dispose();
        }
    }

    private SMTSolverResult checkGoal(Goal g, SolverType solverType) {
        SolverLauncher launcher = new SolverLauncher(new SMTTestSettings());
        SMTProblem problem = new SMTProblem(g);
        launcher.launch(problem, g.proof().getServices(), solverType);
        return problem.getFinalResult();
    }
}
