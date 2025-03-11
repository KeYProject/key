/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testcase.smt.testgen;

import java.io.File;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.macros.TestGenMacro;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;
import de.uka.ilkd.key.suite.util.HelperClassForTestgenTests;
import de.uka.ilkd.key.testcase.smt.ce.TestCommons;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static org.junit.jupiter.api.Assertions.*;
import static org.junit.jupiter.api.Assumptions.assumeFalse;

public class TestTestgen extends TestCommons {
    public static final File testFile =
        new File(HelperClassForTestgenTests.TESTCASE_DIRECTORY, "smt/tg");
    private static final String SYSTEM_PROPERTY_SOLVER_PATH = "z3SolverPath";
    private static final Logger LOGGER = LoggerFactory.getLogger(TestTestgen.class);
    private static boolean isInstalled = false;
    private static boolean installChecked = false;

    @BeforeEach
    public void setup() {
        assumeFalse(toolNotInstalled());
    }

    @Override
    public boolean toolNotInstalled() {
        if (!installChecked) {
            isInstalled = getSolverType().isInstalled(true);
            installChecked = true;
            if (!isInstalled) {
                LOGGER.warn("Warning: {} is not installed, tests skipped.",
                    getSolverType().getName());
                LOGGER.warn(
                    "Maybe use JVM system property \"{}\" to define the path to the Z3 command.",
                    SYSTEM_PROPERTY_SOLVER_PATH);
            }
            if (isInstalled && !getSolverType().supportHasBeenChecked()) {
                if (!getSolverType().checkForSupport()) {
                    LOGGER.warn(
                        "Warning: The version of the solver {} "
                            + "used for the following tests may not be supported.",
                        getSolverType().getName());
                }
            }
        }
        return isInstalled;
    }

    public SolverType getSolverType() {
        SolverType type = SolverTypes.Z3_CE_SOLVER;
        String solverPathProperty = System.getProperty(SYSTEM_PROPERTY_SOLVER_PATH);
        if (solverPathProperty != null && !solverPathProperty.isEmpty()) {
            type.setSolverCommand(solverPathProperty);
        }
        return type;
    }

    @Test
    public void testMiddle() throws Exception {
        File file = new File(testFile, "middle.key");
        assertTrue(file.exists(), "File " + file + " does not exists!");
        KeYEnvironment<DefaultUserInterfaceControl> env =
            KeYEnvironment.load(file, null, null, null);
        try {
            Proof proof = env.getLoadedProof();
            assertNotNull(proof);
            TestGenMacro macro = new TestGenMacro();
            macro.applyTo(env.getUi(), proof, proof.openEnabledGoals(), null, null);
            assertEquals(5, proof.openGoals().size());
        } finally {
            env.dispose();
        }
    }

}
