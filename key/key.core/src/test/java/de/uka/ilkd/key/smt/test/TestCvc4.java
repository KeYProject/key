// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.smt.test;


import de.uka.ilkd.key.smt.st.SolverType;
import de.uka.ilkd.key.smt.st.SolverTypes;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class TestCvc4 extends TestSMTSolver {
    private static final String SYSTEM_PROPERTY_SOLVER_PATH = "cvc4SolverPath";
    private static final Logger LOGGER = LoggerFactory.getLogger(TestCvc4.class);

    private static boolean isInstalled = false;
    private static boolean installChecked = false;


    @Override
    public boolean toolNotInstalled() {
        if (!installChecked) {
            isInstalled = getSolverType().isInstalled(true);
            installChecked = true;
            if (!isInstalled) {
                LOGGER.warn("Warning: {} is not installed, tests skipped.", getSolverType().getName());
                LOGGER.warn("Maybe use JVM system property \"{}\" to define the path to the CVC4 command.",
                        SYSTEM_PROPERTY_SOLVER_PATH);
            }
            if (isInstalled && !getSolverType().supportHasBeenChecked()) {
                if (!getSolverType().checkForSupport()) {
                    LOGGER.warn("Warning: The version of the solver {}" +
                            " used for the following tests may not be supported.", getSolverType().getName());
                }
            }
        }
        return !isInstalled;
    }

    @Override
    public SolverType getSolverType() {
       SolverType type = SolverTypes.CVC4_SOLVER;
        String solverPathProperty = System.getProperty(SYSTEM_PROPERTY_SOLVER_PATH);
        if (solverPathProperty != null && !solverPathProperty.isEmpty()) {
            type.setSolverCommand(solverPathProperty);
        }
        return type;
    }
}