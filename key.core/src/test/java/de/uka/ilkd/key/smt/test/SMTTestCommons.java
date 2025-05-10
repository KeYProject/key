/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.test;

import java.io.File;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.jspecify.annotations.NonNull;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.Tag;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Use this class for testing SMT: It provides a mechanism to load proofs and taclets. Do not modify
 * this class directly but derive subclasses to implement tests.
 */
@Tag("slow")
public abstract class SMTTestCommons {
    protected static final String FOLDER =
        HelperClassForTests.TESTCASE_DIRECTORY + File.separator + "smt"
            + File.separator + "tacletTranslation" + File.separator;
    protected static ProblemInitializer initializer = null;
    protected static final Profile profile = new JavaProfile();

    private TermServices services;

    protected TermServices getServices() {
        return services;
    }

    /**
     * returns the solver that should be tested.
     *
     * @return the solver to be tested.
     */
    public abstract SolverType getSolverType();

    public abstract boolean toolInstalled();

    protected SMTSolverResult.ThreeValuedTruth getResult(SMTSolverResult.ThreeValuedTruth expected,
            String filepath)
            throws ProblemLoaderException {
        Assumptions.assumeTrue(toolInstalled());
        return checkFile(expected, filepath).isValid();
    }

    /**
     * check a problem file
     *
     * @param expected the expected result. Needed for setting a shorter timeout for unknown cases
     * @param filepath the path to the file
     * @return the resulttype of the external solver
     * @throws ProblemLoaderException
     */
    protected SMTSolverResult checkFile(SMTSolverResult.ThreeValuedTruth expected, String filepath)
            throws ProblemLoaderException {
        KeYEnvironment<?> p = loadProof(filepath);
        try {
            Proof proof = p.getLoadedProof();
            assertNotNull(proof);
            assertEquals(1, proof.openGoals().size());
            Goal g = proof.openGoals().iterator().next();
            return checkGoal(expected, g);
        } finally {
            p.dispose();
        }
    }

    private @NonNull SMTSolverResult checkGoal(SMTSolverResult.ThreeValuedTruth expected, Goal g) {
        SMTTestSettings settings = new SMTTestSettings();
        if (expected == SMTSolverResult.ThreeValuedTruth.UNKNOWN) {
            /*
             * Hack: For test cases with unknown/timeout as expected result, we do not want to hold
             * up the test unnecessarily long, so we set a short SMT timeout.
             */
            settings.setTimeout(2000);
        }
        SolverLauncher launcher = new SolverLauncher(settings);
        SMTProblem problem = new SMTProblem(g);
        launcher.launch(problem, g.proof().getServices(), getSolverType());
        return problem.getFinalResult();
    }

    protected KeYEnvironment<?> loadProof(String filepath) throws ProblemLoaderException {
        return KeYEnvironment.load(new File(filepath), null, null, null);
    }

    /**
     * Use this method if you only need taclets for testing.
     */
    protected ProofAggregate parse() {
        return parse(new File(FOLDER + "dummyFile.key"));
    }

    /**
     * Calls <code>parse(File file, Profile profile)</code> with the standard profile for testing.
     */
    protected ProofAggregate parse(File file) {
        return parse(file, profile);
    }

    /**
     * Parses a problem file and returns the corresponding ProofAggregate.
     *
     * @param file problem file.
     * @param pro determines the profile that should be used.
     * @return ProofAggregate of the problem file.
     * @profile determines the profile that should be used.
     */
    protected ProofAggregate parse(File file, Profile pro) {
        assertTrue(file.exists());
        ProofAggregate result = null;
        try {
            KeYUserProblemFile po = new KeYUserProblemFile(file.getName(), file, null, pro);
            if (initializer == null) {
                initializer = new ProblemInitializer(po.getProfile());
            }
            InitConfig initConfig = initializer.prepare(po);
            result = initializer.startProver(initConfig, po);
            services = initConfig.getServices();
            // po.close();
        } catch (Exception e) {
            fail("Error while loading problem file " + file + ":\n\n" + e.getMessage());
        }
        return result;
    }
}
