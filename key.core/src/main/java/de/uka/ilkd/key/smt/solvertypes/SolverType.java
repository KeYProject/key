/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.smt.solvertypes;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.smt.communication.AbstractSolverSocket;


/**
 * This interface is used for modeling different solvers. It provides methods that encode
 * information about the concrete solver: - name - command for starting the solver - parameters -
 * supported versions
 *
 * @author Alexander Weigl
 */
public interface SolverType {

    /**
     * Creates an instance of SMTSolver representing a concrete instance of that solver.
     *
     * @param problem the SMT problem that is sent to the resulting SMT solver process
     * @param listener the listener for the solver process
     * @param services services object to be used by the solver process, if needed (see for example
     *        {@link SMTObjTranslator})
     * @return a concrete solver process of the type at hand
     */
    SMTSolver createSolver(SMTProblem problem, SolverListener listener, Services services);

    /**
     * @return the name of the solver.
     */
    String getName();

    /**
     * Checks whether the solver is installed. If <code>recheck</code> is set to true the method
     * should check for the path variable of the system and for the absolute path, otherwise it can
     * return the result of the previous call.
     *
     * @param recheck if this is true, the installation check will be done again instead of
     *        returning the result from the previous call of this method
     * @return whether the solver is installed (i.e. the command is an existing file)
     */
    boolean isInstalled(boolean recheck);

    /**
     * Some specific information about the solver which can be presented. <code>null</code> means no
     * information.
     *
     * @return the solver-type-specific information, null if there is none
     */
    String getInfo();

    /**
     * Unless {@link #setSolverParameters(String)} is called, these should be the same as
     * {@link #getDefaultSolverParameters()}.
     *
     * @return the currently used parameters for the solver.
     */
    String getSolverParameters();

    /**
     * Set the solver parameters to be used.
     *
     * @param s the new solver parameters
     */
    void setSolverParameters(String s);

    /**
     * @return the default parameters which should be used for starting a solver
     */
    String getDefaultSolverParameters();


    /**
     * The currently used command for starting the solver. For example "z3" if it is registered in
     * the PATH variable, otherwise "ABSOLUTE_PATH/z3". Unless {@link #setSolverCommand(String)} has
     * been called, this should be the same as {@link #getDefaultSolverCommand()}.
     *
     * @return the currently used solver command for starting solver processes
     */
    String getSolverCommand();

    /**
     * Set the solver command to be used for starting processes with the type at hand.
     *
     * @param s the new solver command
     */
    void setSolverCommand(String s);

    /**
     * @return the default solver command for processes of the type at hand
     */
    String getDefaultSolverCommand();

    /**
     * Unless {@link #setSolverTimeout(long)} has been called, this should be the same as
     * {@link #getDefaultSolverTimeout()}.
     *
     * @return the currently set solver timeout, e.g. 2000L milliseconds
     */
    long getSolverTimeout();

    /**
     * Set the timeout for processes with this solver type.
     *
     * @param timeout the new solver timeout
     */
    void setSolverTimeout(long timeout);

    /**
     * @return the default timeout for processes with this solver type.
     */
    long getDefaultSolverTimeout();


    /**
     * @return the translator to be used. So far each solver supports only one format.
     */
    SMTTranslator createTranslator();

    /**
     * Message delimiters used by the solver to separate its messages sent to KeY. For example,
     * those could be "\n".
     *
     * @return the delimiters of the messages that are sent from the solver to KeY.
     */
    String[] getDelimiters();

    /**
     * Directly before the problem description is sent to the solver one can modify the problem
     * string by using this method.
     *
     * @param problem the SMT problem to modify
     * @return the modified SMT problem String
     */
    String modifyProblem(String problem);

    /**
     * @return the parameter that can be used to gain the version of the solver when executing it.
     */
    String getVersionParameter();

    /**
     * @return the minimum supported version of the solver.
     */
    String getMinimumSupportedVersion();

    /**
     * @return the current version that is installed, if it has already been checked, otherwise null
     */
    String getInstalledVersion();

    /**
     * Retrieve the version string without check for support. Returns null if the solver is not
     * installed.
     *
     * @return the installed version of the type at hand, if it is installed - null otherwise
     */
    @Nullable
    String getRawVersion();

    /**
     * @return whether the currently installed version is supported.
     */
    boolean isSupportedVersion();

    /**
     * Checks for support of the solver type's installed version and returns the result.
     *
     * @return true iff the solver type is installed and its version is supported
     */
    boolean checkForSupport();

    /**
     * @return true iff the support has been checked for the currently installed solver.
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
