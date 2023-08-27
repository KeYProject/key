/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;

import java.util.Collection;

import de.uka.ilkd.key.smt.communication.AbstractSolverSocket;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.taclettranslation.assumptions.TacletSetTranslation;

/**
 * The SMTSolver interface represents a solver process (e.g. Z3, Simplify,...) on the KeY side. It
 * is used to store information about an instance of a process and its result. A object of
 * <code>SMTSolver</code> is, therefore, related to exactly one object of typ
 * <code>SMTProblem</code>. Each object of <code>SMTSolver</code> has a specific solver type
 * (<code>SolverType</code>), e.g <code>SolverType.Z3Solver</code>. <br>
 * Note:<br>
 * A class that implements this interface should be thread safe since there methods are accessed by
 * different threads concurrently.
 *
 * @author ?
 */
public interface SMTSolver {

    /**
     * Possible reasons for why a solver process was interrupted/stopped.
     */
    enum ReasonOfInterruption {
        User, Timeout, Exception, NoInterruption
    }

    /**
     * A solver process can have differnt states. When a solver is created, it is in state
     * <code>Waiting</code>. Once it is started it is in state <code>Running</code>. After the
     * execution has stopped the solver is in state <code>Stopped</code>.
     */
    enum SolverState {
        Waiting, Running, Stopped
    }

    /**
     * @return the name of the solver.
     */
    String name();

    /**
     * Returns the translation of the SMTProblem that is handed over to the solver process. If the
     * solver process is still running the method returns <code>null</code> in order to maintain
     * thread safety.
     *
     * @return String representation of the corresponding problem, if the solver process is not
     *         running, otherwise null.
     */
    String getTranslation();

    /**
     * Returns the taclet translation that is used as assumptions. If the solver process is still
     * running the method returns <code>null</code> in order to maintain thread safety.
     *
     * @return the taclet translation that is used as assumptions
     */
    TacletSetTranslation getTacletTranslation();

    /**
     * @return the type of the solver process.
     */
    SolverType getType();

    /**
     * Returns the SMT Problem that is connected to this solver process. If the solver process is
     * still running the method returns <code>null</code> in order to maintain thread safety.
     *
     * @return the SMT Problem that is connected to this solver process
     **/
    SMTProblem getProblem();

    /**
     * If there has occurred an exception while executing the solver process, the method returns
     * this exception, otherwise <code>null</code>
     *
     * @return the exception that occured while executing the solver process, null if none occurred
     */
    Throwable getException();

    /**
     * Use this method in order to interrupt a running solver process.
     *
     * @param reasonOfInterruption The reason of interruption. Can only be set to
     *        <code>ReasonOfInterruption.Timeout</code> or <code>ReasonOfInterruption.User</code>
     *        other wise a <code>IllegalArgumentException</code> is thrown.
     */
    void interrupt(ReasonOfInterruption reasonOfInterruption);

    /**
     * @return the system time when the solver was started. (in ms)
     */
    long getStartTime();

    /**
     * @return the amount of milliseconds after a timeout occurs. (in ms)
     */
    long getTimeout();

    void setTimeout(long timeout);


    /**
     * Returns the current state of the solver. Possible values are<br>
     * <code>Waiting</code>: The solver process is waiting for the start signal<br>
     * <code>Running</code>: The solver process is running <code>Stopped</code>: The solver process
     * was stopped. The reason can be a user interruption, an exception, a timeout or a successful
     * run.
     *
     * @return the current state of the solver process
     */
    SolverState getState();

    /**
     * Returns <code>true</code> if the solver process was interrupted by a user, an exception or a
     * timeout. In all other cases (including that the solver is still running) the method returns
     * <code>false</code>.
     *
     * @return true iff the solver process was interrupted by a user, an exception or a timeout
     */
    boolean wasInterrupted();

    /**
     * @return <code>true</code> if the solver process is running, else <code>false</code>.
     */
    boolean isRunning();

    /**
     * Starts a solver process. This method should be accessed only by an instance of
     * <code>SolverLauncher</code>. If you want to start a solver please have a look at
     * <code>SolverLauncher</code>.
     *
     * @param timeout
     * @param settings
     */
    void start(SolverTimeout timeout, SMTSettings settings);

    /**
     * @return the reason of the interruption: see <code>ReasonOfInterruption</code>.
     */
    ReasonOfInterruption getReasonOfInterruption();

    /**
     * Returns the result of the execution. If the solver process is still running the method
     * returns a result object that represents the result 'unknown'.
     *
     * @return the result of the solver process' execution
     **/
    SMTSolverResult getFinalResult();

    /**
     * Returns the raw solver output. This includes the result (sat/unsat/unknown), possibly
     * error/warning messages, and possibly model/proof as certificate for sat/unsat.
     *
     * <br>
     * <br>
     * <b>Note:</b> Since "endmodel" and "success" are used only for steering the interaction
     * between solver and KeY, these are currently filtered out!
     *
     * @return the raw output of the SMT solver
     */
    String getRawSolverOutput();

    /**
     * Returns the raw solver input. This includes the preamble, the translation of the sequent, and
     * the commands send to the solver to obtain the result(s).
     *
     * @return the complete input that has been sent to the solver
     */
    String getRawSolverInput();

    /**
     * @return the exceptions that have been thrown while translating taclets into assumptions.
     */
    Collection<Throwable> getExceptionsOfTacletTranslation();

    /**
     * @return the solver socket used by the solver process at hand
     */
    AbstractSolverSocket getSocket();

}
