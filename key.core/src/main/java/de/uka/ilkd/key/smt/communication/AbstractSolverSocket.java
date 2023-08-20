/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.communication;

import java.io.IOException;
import javax.annotation.Nonnull;

import de.uka.ilkd.key.smt.ModelExtractor;
import de.uka.ilkd.key.smt.solvertypes.SolverType;

/**
 * The SolverSocket class describes the communication between the KeY and the SMT solver process.
 * This description is no longer part of the SolverType because in the case when we search for
 * counterexamples and one is found, the model has to be queried. This query depends on the SMT
 * problem and is not the same for all solvers of a given type.
 *
 * @author mihai
 * @author Wolfram Pfeifer (overhaul, removed legacy solvers)
 */
public abstract class AbstractSolverSocket {

    /** Indicates that the solver has not yet sent a sat/unsat/unknown result. */
    protected static final int WAIT_FOR_RESULT = 0;

    /** Indicates that the socket waits for more details (a model or a proof). */
    protected static final int WAIT_FOR_DETAILS = 1;

    /** Indicates that the socket waits for the result to a query (used by CE generator). */
    protected static final int WAIT_FOR_QUERY = 2;

    /**
     * Indicates that the socket waits for a model to be produced by the solver. This is a special
     * version of WAIT_FOR_DETAILS only used by the CE generator.
     */
    protected static final int WAIT_FOR_MODEL = 3;

    /** Indicates that the solver already sent a sat/unsat/unknown result. */
    protected static final int FINISH = 4;

    /** The name of the solver related to the socket. */
    private final String name;

    /** The ModelExtractor that is to be used for CE generation (only used for CE socket). */
    private ModelExtractor query;

    /**
     * Creates a new solver socket with given solver name and ModelExtractor.
     *
     * @param name the name of the solver in use
     * @param query the ModelExtractor used to extract a counterexample
     */
    protected AbstractSolverSocket(@Nonnull String name, ModelExtractor query) {
        this.name = name;
        this.query = query;
    }

    public ModelExtractor getQuery() {
        return query;
    }

    public void setQuery(ModelExtractor query) {
        this.query = query;
    }

    protected String getName() {
        return name;
    }

    /**
     * Invoked when the solver has sent a new message to its stdout or stderr.
     *
     * @param pipe the Pipe that received the message
     * @param msg the message as String
     * @throws IOException if an I/O error occurs
     */
    public abstract void messageIncoming(@Nonnull Pipe pipe, @Nonnull String msg)
            throws IOException;

    /**
     * Modify an SMT problem String in some way (e.g. prepend some SMT commands). By default, the
     * String is not changed at all.
     *
     * @param problem the SMT problem String to be modified
     * @return a modified version of the problem
     */
    public String modifyProblem(String problem) {
        return problem;
    }

    /**
     * Creates a new solver socket that can handle the communication for the given solver type.
     *
     * @param type the SolverType to create the socket for
     * @param query the ModelExtractor that can be used to extract a counterexample (for non-CE
     *        solvers this can be null)
     * @return the newly created socket
     */
    public static @Nonnull AbstractSolverSocket createSocket(@Nonnull SolverType type,
            ModelExtractor query) {
        return type.getSocket(query);
    }

    /**
     * @return a shallow copy of the socket at hand (new object with the same class and identical
     *         attributes)
     */
    public abstract AbstractSolverSocket copy();
}
