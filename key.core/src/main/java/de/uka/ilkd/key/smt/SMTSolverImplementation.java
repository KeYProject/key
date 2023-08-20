/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;

import java.io.IOException;
import java.util.Collection;
import java.util.LinkedList;
import java.util.concurrent.atomic.AtomicInteger;
import javax.annotation.Nonnull;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.smt.communication.AbstractSolverSocket;
import de.uka.ilkd.key.smt.communication.ExternalProcessLauncher;
import de.uka.ilkd.key.smt.communication.SolverCommunication;
import de.uka.ilkd.key.smt.communication.SolverCommunication.Message;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;
import de.uka.ilkd.key.taclettranslation.assumptions.TacletSetTranslation;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Represents a concrete instance of a running solver process on the KeY side. Amongst others
 * performs the following steps:
 * <ol>
 * <li>Translates the given problem to SMT format.</li>
 * <li>Starts the external solver process.</li>
 * <li>Sends the problem to the process.</li>
 * <li>Communicates with the solver via the solver socket.</li>
 * </ol>
 *
 * @author ?
 * @author Wolfram Pfeifer (SMT communication overhaul)
 */
public final class SMTSolverImplementation implements SMTSolver, Runnable {
    private static final Logger LOGGER = LoggerFactory.getLogger(SMTSolverImplementation.class);

    /**
     * used to generate unique ids for each running solver instance
     */
    private static final AtomicInteger ID_COUNTER = new AtomicInteger();

    /**
     * the unique id of this solver
     */
    private final int id = ID_COUNTER.incrementAndGet();

    /**
     * the socket that handles solver results and interactively communicates with the running
     * external solver process
     */
    private final @Nonnull AbstractSolverSocket socket;

    /**
     * the ModelExtractor used to generate counterexamples (only used for CE solver type)
     */
    private ModelExtractor query;

    /**
     * The SMT problem that is related to this solver
     */
    private final SMTProblem problem;

    /**
     * It is possible that a solver has a listener.
     */
    private final SolverListener listener;

    /**
     * starts a external process and returns the result
     */
    private final ExternalProcessLauncher processLauncher;

    /**
     * The services object is stored in order to have the possibility to access it in every method
     */
    private final Services services;

    /**
     * The record of the communication between KeY and the given solver. If everything works fine,
     * it also contains the final result.
     */
    private final SolverCommunication solverCommunication = new SolverCommunication();

    /**
     * The thread that is associated with this solver.
     */
    private Thread thread;

    /**
     * The timeout that is associated with this solver. Represents the timertask that is started
     * when the solver is started.
     */
    private SolverTimeout solverTimeout;

    /**
     * stores the reason for interruption if present (e.g. User, Timeout, Exception)
     */
    private ReasonOfInterruption reasonOfInterruption = ReasonOfInterruption.NoInterruption;

    /**
     * the state the solver is currently in
     */
    private SolverState solverState = SolverState.Waiting;

    /**
     * the type of this solver (Z3, CVC4, Z3_CE, ...)
     */
    private final SolverType type;

    /**
     * Stores the settings that are used for the execution.
     */
    private SMTSettings smtSettings;

    /**
     * Stores the translation of the problem that is associated with this solver
     */
    private String problemString = "NOT YET COMPUTED";

    /**
     * Stores the taclet translation that is associated with this solver.
     */
    private TacletSetTranslation tacletTranslation;

    /**
     * If there was an exception while executing the solver it is stored in this attribute.
     */
    private Throwable exception;

    /**
     * the exceptions that may occur during taclet translation
     */
    private final Collection<Throwable> exceptionsForTacletTranslation = new LinkedList<>();

    /**
     * The timeout in seconds for this SMT solver run.
     */
    private long timeout = -1;

    /**
     * Creates a new instance an SMT solver.
     *
     * @param problem the problem to send to the external solver process
     * @param listener the listener that has to be informed when the solver state changes
     * @param services the services needed to translate the problem to SMT format
     * @param myType the type of the solver to run (e.g., Z3, CVC3, Z3_CE)
     */
    public SMTSolverImplementation(SMTProblem problem, SolverListener listener, Services services,
            SolverType myType) {
        this.problem = problem;
        this.listener = listener;
        this.services = services;
        this.type = myType;
        // Why not just call type.getSocket(query) here?
        this.socket = AbstractSolverSocket.createSocket(type, query);
        processLauncher = new ExternalProcessLauncher(solverCommunication, myType.getDelimiters());
    }

    /**
     * Starts a solver process. This method should be accessed only by an instance of
     * <code>SolverLauncher</code>. If you want to start a solver please have a look at
     * <code>SolverLauncher</code>.
     *
     * @param timeout the timeout to use for the solver
     * @param settings the SMTSettings to use for this solver
     */
    @Override
    public void start(SolverTimeout timeout, SMTSettings settings) {
        thread = new Thread(this, "SMTProcessor");
        solverTimeout = timeout;
        smtSettings = settings;
        thread.start();
    }

    @Override
    public ReasonOfInterruption getReasonOfInterruption() {
        return isRunning() ? ReasonOfInterruption.NoInterruption : reasonOfInterruption;
    }

    public Throwable getException() {
        return isRunning() ? null : exception;
    }

    public SMTProblem getProblem() {
        return isRunning() ? null : problem;
    }

    public void setReasonOfInterruption(ReasonOfInterruption reasonOfInterruption) {
        this.reasonOfInterruption = reasonOfInterruption;
    }

    private void setReasonOfInterruption(ReasonOfInterruption reasonOfInterruption, Throwable exc) {
        this.reasonOfInterruption = reasonOfInterruption;
        this.exception = exc;
    }

    @Override
    public SolverType getType() {
        return type;
    }

    @Override
    public long getStartTime() {
        if (solverTimeout == null) {
            return -1;
        }
        return solverTimeout.scheduledExecutionTime();
    }

    @Override
    public long getTimeout() {
        return timeout;
    }

    @Override
    public void setTimeout(long timeout) {
        this.timeout = timeout;
    }

    @Override
    public SolverState getState() {
        return solverState;
    }

    private void setSolverState(SolverState value) {
        solverState = value;
    }

    @Override
    public boolean wasInterrupted() {
        return getReasonOfInterruption() != ReasonOfInterruption.NoInterruption;
    }

    @Override
    public boolean isRunning() {
        return getState() == SolverState.Running;
    }


    @Override
    public void run() {

        // Firstly: Set the state to running and inform the listener.
        setSolverState(SolverState.Running);
        listener.processStarted(this, problem);

        // Secondly: Translate the given problem
        String[] commands;
        try {
            commands = translateToCommand(problem.getSequent());
        } catch (IllegalFormulaException e) {
            interruptionOccurred(e);
            listener.processInterrupted(this, problem, e);
            setSolverState(SolverState.Stopped);
            solverTimeout.cancel();
            return;
        }

        // Thirdly: start the external process.
        try {
            processLauncher.launch(commands);
            processLauncher.getPipe().sendMessage(type.modifyProblem(problemString));
            // processLauncher.getPipe().sendEOF();

            String msg = processLauncher.getPipe().readMessage();
            while (msg != null) {
                socket.messageIncoming(processLauncher.getPipe(), msg);
                msg = processLauncher.getPipe().readMessage();
            }
        } catch (IllegalStateException | IOException | InterruptedException e) {
            interruptionOccurred(e);
            Thread.currentThread().interrupt();
        } finally {
            // Close everything.
            solverTimeout.cancel();
            setSolverState(SolverState.Stopped);
            listener.processStopped(this, problem);
            processLauncher.stop();
        }
    }

    private void interruptionOccurred(Throwable e) {
        ReasonOfInterruption reason = getReasonOfInterruption();
        setReasonOfInterruption(ReasonOfInterruption.Exception, e);
        switch (reason) {
        case Exception:
        case NoInterruption:
            setReasonOfInterruption(ReasonOfInterruption.Exception, e);
            listener.processInterrupted(this, problem, e);
            break;
        case Timeout:
            listener.processTimeout(this, problem);
            break;
        case User:
            listener.processUser(this, problem);
            break;
        }
    }

    @Override
    public String name() {
        return type.getName();
    }

    private static String indent(String string) {
        try {
            return SMTBeautifier.indent(string);
        } catch (Exception ex) {
            // fall back if pretty printing fails
            LOGGER.warn("Beautifier failed", ex);
            return string;
        }
    }

    private String[] translateToCommand(Sequent sequent) throws IllegalFormulaException {
        if (getType() == SolverTypes.Z3_CE_SOLVER) {
            Proof proof = problem.getGoal().proof();
            SpecificationRepository specrep = proof.getServices().getSpecificationRepository();

            Proof originalProof = null;
            for (Proof pr : specrep.getAllProofs()) {
                if (proof.name().toString().endsWith(pr.name().toString())) {
                    originalProof = pr;
                    break;
                }
            }

            KeYJavaType typeOfClassUnderTest =
                specrep.getProofOblInput(originalProof).getContainerType();

            SMTObjTranslator objTrans =
                new SMTObjTranslator(smtSettings, services, typeOfClassUnderTest);
            problemString = objTrans.translateProblem(sequent, services, smtSettings).toString();
            ModelExtractor transQuery = objTrans.getQuery();
            getSocket().setQuery(transQuery);
            tacletTranslation = null;

        } else {
            SMTTranslator trans = getType().createTranslator();
            problemString =
                indent(trans.translateProblem(sequent, services, smtSettings).toString());
            if (trans instanceof AbstractSMTTranslator) {
                // Since taclet translation in the old form is no longer used,
                // this will likely disappear.
                exceptionsForTacletTranslation
                        .addAll(((AbstractSMTTranslator) trans).getExceptionsOfTacletTranslation());
            }
        }

        String[] parameters = this.type.getSolverParameters().split(" ");
        String[] result = new String[parameters.length + 1];
        for (int i = 0; i < result.length; i++) {
            result[i] = i == 0 ? type.getSolverCommand() : parameters[i - 1];
        }
        return result;
    }

    @Override
    public void interrupt(ReasonOfInterruption reason) {
        // order of assignments is important
        setReasonOfInterruption(reason);
        setSolverState(SolverState.Stopped);
        if (solverTimeout != null) {
            solverTimeout.cancel();
        }
        if (thread != null) {
            processLauncher.stop();
            thread.interrupt();
        }
    }

    @Override
    public SMTSolverResult getFinalResult() {
        return isRunning() ? null : solverCommunication.getFinalResult();
    }

    @Override
    public TacletSetTranslation getTacletTranslation() {
        return isRunning() ? null : tacletTranslation;
    }

    @Override
    public String getTranslation() {
        return isRunning() ? null : problemString;
    }

    @Override
    public String toString() {
        return name() + " (ID: " + id + ")";
    }

    @Override
    public String getRawSolverOutput() {
        StringBuilder output = new StringBuilder();
        for (Message m : solverCommunication.getOutMessages()) {
            String s = m.getContent();
            output.append(s).append("\n");
        }
        return output.toString();
    }

    @Override
    public String getRawSolverInput() {
        StringBuilder input = new StringBuilder();

        for (Message m : solverCommunication.getMessages(SolverCommunication.MessageType.INPUT)) {
            String s = m.getContent();
            input.append(s).append("\n");
        }
        return input.toString();
    }

    @Override
    public Collection<Throwable> getExceptionsOfTacletTranslation() {
        return exceptionsForTacletTranslation;
    }

    @Override
    public AbstractSolverSocket getSocket() {
        return socket;
    }

    public ModelExtractor getQuery() {
        return query;
    }

    public void setQuery(ModelExtractor query) {
        this.query = query;
    }
}
