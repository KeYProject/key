// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.smt;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.Calendar;
import java.util.Collection;
import java.util.LinkedList;
import java.util.concurrent.locks.ReentrantLock;
import java.util.regex.Matcher;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.taclettranslation.assumptions.TacletSetTranslation;
import de.uka.ilkd.key.util.Debug;

interface SolverListener {
        void processStarted(SMTSolver solver, SMTProblem problem);

        void processInterrupted(SMTSolver solver, SMTProblem problem,
                        Throwable e);

        void processStopped(SMTSolver solver, SMTProblem problem);

        void processTimeout(SMTSolver solver, SMTProblem problem);

        void processUser(SMTSolver solver, SMTProblem problem);
}

final class SMTSolverImplementation implements SMTSolver, Runnable{

        private static int fileCounter = 0;

        private static synchronized int getNextFileID() {
                fileCounter++;
                return fileCounter;
        }

        private static int IDCounter = 0;
        private final int ID = IDCounter++;

        /**
         * the file base name to be used to store the SMT translation
         */
        private static final String FILE_BASE_NAME = "smt_formula";

        /** The SMT problem that is related to this solver */
        private SMTProblem problem;
        /** It is possible that a solver has a listener. */
        private SolverListener listener;

        /** starts a external process and returns the result */
        private ExternalProcessLauncher<SolverCommunication> processLauncher 
        	= new ExternalProcessLauncher<SolverCommunication>(new SolverCommunication());
        /**
         * The services object is stored in order to have the possibility to
         * access it in every method
         */
        private Services services;
        /**
         * The record of the communication between KeY and the given solver. If everything works fine,
         * it also contains the final result.
         */
        private SolverCommunication solverCommunication = SolverCommunication.EMPTY;
      

        /**
         * This lock variable is responsible for the state variable
         * <code>sovlerState</code>
         */
        private ReentrantLock lockStateVariable = new ReentrantLock();
        /**
         * This lock variable is responsible for the attribute
         * <code>reasonOfInterruption</code>
         */
        private ReentrantLock lockInterruptionVariable = new ReentrantLock();

        /** The thread that is associated with this solver. */
        private Thread thread;
        /**
         * The timeout that is associated with this solver. Represents the
         * timertask that is started when the solver is started.
         */
        private SolverTimeout solverTimeout;

        private ReasonOfInterruption reasonOfInterruption = ReasonOfInterruption.NoInterruption;
        private SolverState solverState = SolverState.Waiting;

        private final SolverType type;
        /** Strores the settings that are used for the execution. */
        private SMTSettings smtSettings;

        /**
         * Stores the translation of the problem that is associated with this
         * solver
         */
        private String problemString = "NOT YET COMPUTED";
        /** Stores the taclet translation that is associated with this solver. */
        private TacletSetTranslation tacletTranslation;
        /**
         * If there was an exception while executing the solver it is stored in
         * this attribute
         */
        private Throwable exception;
        
        private Collection<Throwable> exceptionsForTacletTranslation = new LinkedList<Throwable>();

 


        SMTSolverImplementation(SMTProblem problem, SolverListener listener,
                        Services services, SolverType myType) {
                this.problem = problem;
                this.listener = listener;
                this.services = services;
                this.type = myType;

        }

        /**
         * Starts a solver process. This method should be accessed only by an
         * instance of <code>SolverLauncher</code>. If you want to start a
         * solver please have a look at <code>SolverLauncher</code>.
         * 
         * @param timeout
         * @param settings
         */
        public void start(SolverTimeout timeout, SMTSettings settings) {
                thread = new Thread(this);
                solverTimeout = timeout;
                smtSettings = settings;
                thread.start();
        }

        @Override
        public ReasonOfInterruption getReasonOfInterruption() {
                return isRunning() ? ReasonOfInterruption.NoInterruption
                                : reasonOfInterruption;
        }

        public Throwable getException() {
                return isRunning() ? null : exception;
        }

        public SMTProblem getProblem() {
                return isRunning() ? null : problem;
        }

        public void setReasonOfInterruption(
                        ReasonOfInterruption reasonOfInterruption) {
                try {
                        lockInterruptionVariable.lock();
                        this.reasonOfInterruption = reasonOfInterruption;
                } finally {
                        lockInterruptionVariable.unlock();
                }
        }

        private void setReasonOfInterruption(
                        ReasonOfInterruption reasonOfInterruption, Throwable exc) {
                try {
                        lockInterruptionVariable.lock();
                        this.reasonOfInterruption = reasonOfInterruption;
                        this.exception = exc;
                } finally {
                        lockInterruptionVariable.unlock();
                }
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
                if (solverTimeout == null) {
                        return -1;
                }
                return solverTimeout.getTimeout();
        }

        @Override
        public SolverState getState() {
                try {
                        lockStateVariable.lock();
                        SolverState b = solverState;
                        return b;
                } finally { // finally trumps return
                        lockStateVariable.unlock();
                }
        }

        private void setSolverState(SolverState value) {
                try {
                        lockStateVariable.lock();
                        solverState = value;
                } finally { // finally trumps return
                        lockStateVariable.unlock();
                }
        }

        @Override
        public boolean wasInterrupted() {
                return getReasonOfInterruption() != ReasonOfInterruption.NoInterruption;
        }

        @Override
        public boolean isRunning() {
                return getState() == SolverState.Running;
        }

        private String []getFinalExecutionCommand(String filename, String formula) {
                // get the Command from user settings
                String toReturn = this.type.getSolverParameters();
                  // replace the placeholder with filename and fomula
         
                toReturn = toReturn.replaceAll("%f",Matcher.quoteReplacement(filename));
                toReturn = toReturn.replaceAll("%p", formula);
                
                
                return toReturn.split(" ");
        }

        @Override
        public void run() {
                // Firstly: Set the state to running and inform the listener.
                setSolverState(SolverState.Running);
                listener.processStarted(this, problem);

                // Secondly: Translate the given problem
                String commands[];
                try {
                        commands = translateToCommand(problem.getTerm());
                } catch (Throwable e) {
                        interruptionOccurred(e);
                        listener.processInterrupted(this, problem, e);
                        setSolverState(SolverState.Stopped);
                        solverTimeout.cancel();
                        return;
                }
     

                // start the external process.
                try {
                        processLauncher.launch(commands,problemString,type);
                        solverCommunication = processLauncher.getCommunication();
                        if(solverCommunication.exceptionHasOccurred() && 
                          !solverCommunication.resultHasBeenSet()){ 
                        	// if the result has already been set, the exceptions 
                        	// must have occurred while doing the remaining communication, which is not that important.
                        	throw new AccumulatedException(solverCommunication.getExceptions());
                        }
                                      
                        // uncomment for testing
                        //Thread.sleep(5000);
                        // uncomment for testing
                       // Random random = new Random();
                        //Thread.sleep(random.nextInt(3000)+1000);
                       // throw new RuntimeException("Test exception");
                } catch (Throwable e) {
                        interruptionOccurred(e);
                } finally {
                        // Close every thing.
                        solverTimeout.cancel();
                        setSolverState(SolverState.Stopped);
                        listener.processStopped(this, problem);
                }

        }

        private void interruptionOccurred(Throwable e) {
                ReasonOfInterruption reason = getReasonOfInterruption();
                switch (reason) {
                case Exception:
                case NoInterruption:
                        setReasonOfInterruption(ReasonOfInterruption.Exception,
                                        e);
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

        private static String toStringLeadingZeros(int n, int width) {
                String rv = "" + n;
                while (rv.length() < width) {
                        rv = "0" + rv;
                }
                return rv;
        }

        /**
         * Constructs a date for use in log filenames.
         */
        private static String getCurrentDateString() {
                Calendar c = Calendar.getInstance();
                StringBuffer sb = new StringBuffer();
                String dateSeparator = "-";
                String dateTimeSeparator = "_";
                sb.append(toStringLeadingZeros(c.get(Calendar.YEAR), 4))
                                .append(dateSeparator)
                                .append(toStringLeadingZeros(
                                                c.get(Calendar.MONTH) + 1, 2))
                                .append(dateSeparator)
                                .append(toStringLeadingZeros(
                                                c.get(Calendar.DATE), 2))
                                .append(dateTimeSeparator)
                                .append(toStringLeadingZeros(
                                                c.get(Calendar.HOUR_OF_DAY), 2))
                                .append("h")
                                .append(toStringLeadingZeros(
                                                c.get(Calendar.MINUTE), 2))
                                .append("m")
                                .append(toStringLeadingZeros(
                                                c.get(Calendar.SECOND), 2))
                                .append("s")
                                .append('.')
                                .append(toStringLeadingZeros(
                                                c.get(Calendar.MILLISECOND), 2));
                return sb.toString();
        }

        /**
         * store the text to a file.
         * 
         * @param text
         *                the text to be stored.
         * @return the path where the file was stored to.
         */
        private final File storeToFile(String text) throws IOException {
                // create directory where to put the files marked as delete on
                // exit
                final File smtFileDir = new File(
                                smtSettings.getSMTTemporaryFolder());
                smtFileDir.mkdirs();
                smtFileDir.deleteOnExit();

                // create the actual file marked as delete on exit
                final File smtFile = new File(smtFileDir, FILE_BASE_NAME + "_"
                                + name() + "_" + "_" + getNextFileID() + "_"
                                + getCurrentDateString());

                smtFile.deleteOnExit();

                // write the content out to the created file
                // final BufferedWriter out = new BufferedWriter(new
                // FileWriter(smtFile));
                final FileWriter out = new FileWriter(smtFile);
                out.write(text);
                out.close();

                return smtFile;
        }

        /**
         * Read the input until end of file and return contents in a single
         * string containing all line breaks.
         */
        static String read(InputStream in) throws IOException {
                BufferedReader reader = new BufferedReader(
                                new InputStreamReader(in));
                StringBuffer sb = new StringBuffer();

                int x = reader.read();
                while (x > -1) {
                        sb.append((char) x);
                        x = reader.read();
                }
                return sb.toString();
        }

        private String [] translateToCommand(String formula) throws IOException {
                final File loc;
                try {
                        // store the translation to a file
                        loc = this.storeToFile(formula);
                } catch (IOException e) {
                        Debug.log4jError(
                                        "The file with the formula could not be written."
                                                        + e,
                                        SMTSolverImplementation.class.getName());
                        final IOException io = new IOException(
                                        "Could not create or write the input file "
                                                        + "for the external prover. Received error message:\n"
                                                        + e.getMessage());
                        io.initCause(e);
                        throw io;
                }
         
                // get the commands for execution
                return this.getFinalExecutionCommand(loc.getAbsolutePath(),
                                formula);
        }

        private String[] translateToCommand(Term term)
                        throws IllegalFormulaException, IOException {

                SMTTranslator trans = getType().getTranslator(services);
                // instantiateTaclets(trans);
         
                problemString = trans.translateProblem(term, services,
                                smtSettings).toString();
            
                tacletTranslation = ((AbstractSMTTranslator) trans)
                                .getTacletSetTranslation();
                exceptionsForTacletTranslation.addAll(trans.getExceptionsOfTacletTranslation());
                String parameters [] = translateToCommand(problemString);
                String result [] = new String[parameters.length+1];
                for(int i=0; i < result.length; i++){
                    result[i] = i==0? type.getSolverCommand() : parameters[i-1];
                }
                return result;
        }

        @Override
        public void interrupt(ReasonOfInterruption reason) {

                // order of assignments is important;
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
                return name() + " (ID: " + ID + ")";
        }

        @Override
        public String getSolverOutput() {
         		String output = "";
        		output+= "Result: "+ solverCommunication.getFinalResult().toString()+"\n\n";
      	
      
        		for(String s : solverCommunication.getMessages()){
        			output += s+"\n";
        		}
                return output;
        }

        @Override
        public Collection<Throwable> getExceptionsOfTacletTranslation() {
                
                return exceptionsForTacletTranslation;
        }


}
