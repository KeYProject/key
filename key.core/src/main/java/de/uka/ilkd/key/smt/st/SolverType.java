/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.smt.st;

import javax.annotation.Nonnull;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.smt.communication.AbstractSolverSocket;


/**
 * This interface is used for modeling different solvers. It provides methods that encode
 * information
 * about the concrete solver:
 * - name
 * - command for starting the solver
 * - parameters
 * - supported versions
 */
public interface SolverType {

    /**
     * Creates an instance of SMTSolver representing a concrete instance of that solver.
     */
    SMTSolver createSolver(SMTProblem problem,
            SolverListener listener, Services services);

    /**
     * Returns the name of the solver.
     */
    String getName();

    /**
     * Checks whether the solver is installed. If <code>recheck</code> is set to true
     * the method should check for the path variable of the system and for the absolute path,
     * otherwise it can return the result of the previous call.
     */
    boolean isInstalled(boolean recheck);

    /**
     * Some specific information about the solver which can be presented. <code>null</code> means no
     * information.
     */
    String getInfo();

    /**
     * The currently used parameters for the solver.
     */
    String getSolverParameters();

    void setSolverParameters(String s);

    /**
     * The default parameters which should be used for starting a solver
     */
    String getDefaultSolverParameters();


    /**
     * the command for starting the solver. For example "z3" if it is registered in the PATH
     * variable,
     * otherwise "ABSOLUTE_PATH/z3"
     */
    String getSolverCommand();

    void setSolverCommand(String s);

    String getDefaultSolverCommand();


    /**
     * The translator to be used. So far each solver supports only one format.
     */
    SMTTranslator createTranslator(Services services);

    /**
     * The delimiters of the messages that are sent from the solver to KeY. For example, it could be
     * "\n"
     */
    String[] getDelimiters();

    /**
     * Returns true if and only if the solver supports if-then-else terms.
     */
    boolean supportsIfThenElse();

    /**
     * Directly before the problem description is sent to the solver one can modify the problem
     * string by using
     * this method.
     */
    String modifyProblem(String problem);

    /**
     * Returns the parameter that can be used to gain the version of the solver when
     * executing it.
     */
    String getVersionParameter();

    /**
     * Returns an array of all versions that are supported by KeY.
     */
    String[] getSupportedVersions();

    /**
     * Returns the current version that is installed, if it has already been checked, otherwise
     * null.
     */
    String getVersion();

    /**
     * Retrieve the version string without check for support.
     * Returns null if the solver is not installed.
     */
    String getRawVersion();

    /**
     * Returns whether the currently installed version is supported.
     */
    boolean isSupportedVersion();

    /**
     * Checks for support and returns the result.
     */
    boolean checkForSupport();

    /**
     * returns true if and only if the support has been checked for the currently installed solver.
     */
    boolean supportHasBeenChecked();

    /**
     * Creates a new solver socket that can handle the communication for the given solver type.
     *
     * @param query the ModelExtractor that can be used to extract a counterexample (for non-CE
     *        solvers this can be null)
     * @return the newly created socket
     */
    @Nonnull
    AbstractSolverSocket getSocket(ModelExtractor query);
}
