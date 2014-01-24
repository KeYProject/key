// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.smt;

import java.util.Collection;

import de.uka.ilkd.key.taclettranslation.assumptions.TacletSetTranslation;

/**
 * The SMTSolver interface represents a solver process (e.g. Z3, Simplify,...)
 * on the KeY side. It is used to store information about an instance of a
 * process and its result. A object of <code>SMTSolver</code> is, therefore,
 * related to exactly one object of typ <code>SMTProblem</code>. Each object of
 * <code>SMTSolver</code> has a specific solver type (<code>SolverType</code>),
 * e.g <code>SolverType.Z3Solver</code>. <br>
 * Note:<br>
 *A class that implements this interface should be thread safe since there
 * methods are accessed by different threads concurrently.
 * 
 */
public interface SMTSolver {

    public enum ReasonOfInterruption {
	User, Timeout, Exception, NoInterruption
    }

    /**
     * A solver process can have differnt states. When a solver is created, it
     * is in state <code>Waiting</code>. Once it is started it is in state
     * <code>Running</code>. After the execution has stopped the solver is in
     * state <code>Stopped</code>.
     */
    public enum SolverState {
	Waiting, Running, Stopped
    }

    /**
     * Returns the name of the solver.
     */
    public String name();

    /**
     * Returns the translation of the SMTProblem that is handed over to the
     * solver process. If the solver process is still running the method returns
     * <code>null</code> in order to maintain thread safety.
     * 
     * @return String representation of the corresponding problem, if the solver
     *         process is not running, otherwise null.
     */
    public String getTranslation();

    /**
     * Returns the taclet translation that is used as assumptions. If the solver
     * process is still running the method returns <code>null</code> in order to
     * maintain thread safety.
     */
    public TacletSetTranslation getTacletTranslation();

    /**
     * Returns the type of the solver process.
     */
    public SolverType getType();

    /**
     * Returns the SMT Problem that is connected to this solver process. If the
     * solver process is still running the method returns <code>null</code> in
     * order to maintain thread safety.
     **/
    public SMTProblem getProblem();

    /**
     * If there has occurred an exception while executing the solver process,
     * the method returns this exceptions, otherwise <code>null</code>
     * 
     */
    public Throwable getException();

    /**
     * Use this method in order to interrupt a running solver process.
     * 
     * @param reasonOfInterruption
     *            The reason of interruption. Can only be set to
     *            <code>ReasonOfInterruption.Timeout</code> or
     *            <code>ReasonOfInterruption.User</code> other wise a
     *            <code>IllegalArgumentException</code> is thrown.
     */
    public void interrupt(ReasonOfInterruption reasonOfInterruption);

    /**
     * Returns the system time when the solver was started. (in ms)
     */
    public long getStartTime();

    /**
     * Returns the amount of milliseconds after a timeout occurs. (in ms)
     */
    public long getTimeout();

    /**
     * Returns the current state of the solver. Possible values are<br>
     * <code>Waiting<\code>: The solver process is waiting for the start signal<br>
     * <code>Running<\code>: The solver process is running
     * <code>Stopped<\code>: The solver process was stopped. The reason can be a user interruption, 
     * an exception, a timeout or a successfull run.
     */
    public SolverState getState();

    /**
     * Returns <code>true</code> if the solver process was interrupted by an
     * user, an exception or a timeout. In all other cases (including that the
     * solver is still running) the method returns <code>true</code>.
     * */
    public boolean wasInterrupted();

    /**
     * Returns <code>true</code> if the solver process is running else
     * <code>false</code>.
     */
    public boolean isRunning();

    /**
     * Returns the reason of the interruption: see
     * <code>ReasonOfInterruption</code>.
     */
    public ReasonOfInterruption getReasonOfInterruption();

    /**
     * Returns the result of the execution. If the solver process is still
     * running the method returns a result object that represents the result
     * 'unknown'.
     **/
    public SMTSolverResult getFinalResult();
    
    /**
     * Returns the solver output without any change. 
     * The format is:
     * "
     * Normal Output:
     * ...
     * 
     * Error Output:
     * ...
     * Exit Code: ...
     * "
     */
    public String getSolverOutput();
    
    /**
     * Returns the exceptions that has been thrown while translating taclets into assumptions. 
     */
    public Collection<Throwable> getExceptionsOfTacletTranslation();

}
