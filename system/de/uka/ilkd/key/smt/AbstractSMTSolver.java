//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                    Universitaet Koblenz-Landau, Germany
//                    Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.smt;


import java.io.*;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.Collection;
import java.util.Date;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Timer;

import javax.management.ImmutableDescriptor;
import javax.swing.JFileChooser;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.DecisionProcedureSettings;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.configuration.PathConfig;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.smt.launcher.AbstractProcess;
import de.uka.ilkd.key.smt.taclettranslation.DefaultTacletSetTranslation;
import de.uka.ilkd.key.smt.taclettranslation.IllegalTacletException;
import de.uka.ilkd.key.smt.taclettranslation.TacletFormula;
import de.uka.ilkd.key.smt.taclettranslation.TacletSetTranslation;
import de.uka.ilkd.key.smt.taclettranslation.UsedTaclets;
import de.uka.ilkd.key.util.ProgressMonitor;


public abstract class AbstractSMTSolver extends AbstractProcess implements SMTSolver {

    
    private static int fileCounter = 0;

    private static final Logger logger = Logger
	    .getLogger(AbstractSMTSolver.class.getName());

    /**
     * The path for the file
     */
    private static final String fileDir = PathConfig.KEY_CONFIG_DIR
	    + File.separator + "smt_formula";

    /**
     * the file base name to be used to store the SMT translation
     */
    private static final String FILE_BASE_NAME = "smt_formula";
    
    /** true, if this solver was checked if installed */
    private boolean installwaschecked = false;
    /** true, if last check showed solver is installed */
    private boolean isinstalled = false;
    /** true, if the current run is for test uss only (for example checking, if the Solver is installed) */
    private boolean inTestMode = false;

    /** determines whether taclets are used for this solver.*/
    private boolean useTaclets = true;
    /** Only for testing*/
    private Collection<Taclet> tacletsForTest = null;
    /** true, if the solver should save the translated taclets to file. */
    private boolean saveTacletTranslation = true;
    
    private SolverSession session = null;
    
    public SolverSession getSession(){return session;}
    
    private boolean useForMultipleRule = false;
    
    private String   executionCommand = getDefaultExecutionCommand();
    
    
    
    public AbstractSMTSolver(){
	//isInstalled(true);
    }


    /**
     * Get the command for executing the external prover.
     * This is a hardcoded default value. It might be overridden by user settings
     * @param filename the location, where the file is stored.
     * @param formula the formula, that was created by the translator
     * @return Array of Strings, that can be used for executing an external decider.
     */
    protected abstract String getExecutionCommand(String filename,
	    				            String formula);
  
    public SMTTranslator getTranslator(Services services) {
	try{
	    final DecisionProcedureSettings dps = ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings();
	    if(dps.weakenSMTTranslation){
		return new SmtLibTranslatorWeaker(services);
	    }else{
		return new SmtLibTranslator(services);
	    }
	}catch(Exception e){
	    System.err.println("Error: An error occurred while obtaining an SmtLibTranslator: Trying to use the default translator...");
	    e.printStackTrace();
	    return new SmtLibTranslator(services);
	}
    }

    
    private String getFinalExecutionCommand(String filename, String formula) {
	//get the Command from user settings
	String toReturn = ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().getExecutionCommand(this);
	if (toReturn == null || toReturn.length() == 0) {
	    toReturn = this.getExecutionCommand(filename, formula);
	} else {
	    //replace the placeholder with filename and fomula
	    toReturn = toReturn.replaceAll("%f", filename);
	    toReturn = toReturn.replaceAll("%p", formula);
	}
	return toReturn;
    }
    
   
    
  /*  /**
     * Interpret the answer of the program.
     * This is very solverdepending. Usually, an exitcode of 0 inicates no error.
     * But not every solver returns 0 if successfull termination was reached.
     * @param output the String answered by the external programm.
     * @param error the String answered as error
     * @param exitstatus the status of the exit
     * @return A SMTSolverResult containing all information of the interpretation.
     * @throws IllegalArgumentException If the solver caused an error.
     */
   // public abstract SMTSolverResult interpretAnswer(String output, String error, int exitstatus) throws IllegalArgumentException;

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
        sb.append(toStringLeadingZeros(c.get(Calendar.YEAR), 4)).append(
                dateSeparator).append(
                toStringLeadingZeros(c.get(Calendar.MONTH) + 1, 2)).append(
                dateSeparator).append(
                toStringLeadingZeros(c.get(Calendar.DATE), 2)).append(
                dateTimeSeparator).append(toStringLeadingZeros(c.get(Calendar.HOUR_OF_DAY), 2)).
                append("h").append(toStringLeadingZeros(c.get(Calendar.MINUTE), 2)).append("m").
                append(toStringLeadingZeros(c.get(Calendar.SECOND), 2)).append("s")
		        .append('.').append(
			toStringLeadingZeros(c.get(Calendar.MILLISECOND), 2));
	return sb.toString();
    }

    /**
     * store the text to a file.
     * @param text the text to be stored.
     * @return the path where the file was stored to.
     */
    private final File storeToFile(String text) throws IOException {
	// create directory where to put the files marked as delete on exit
	final File smtFileDir = new File(fileDir);
	smtFileDir.mkdirs();
	smtFileDir.deleteOnExit();
	
	// create the actual file marked as delete on exit
	final File smtFile = new File(smtFileDir, FILE_BASE_NAME +"_"+fileCounter+"_"+ getCurrentDateString());
	fileCounter++;
	smtFile.deleteOnExit();
	
	// write the content out to the created file
	final BufferedWriter out = new BufferedWriter(new FileWriter(smtFile));
	out.write(text);
	out.close();

	//store the text permanent to a file 
	if (!this.inTestMode && ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().getSaveFile() &&
		Main.getInstance() != null) {
	    JFileChooser fc = new JFileChooser();
	    fc.setDialogTitle("Select a file to save the created problem");
	    fc.setMultiSelectionEnabled(false);
	    int returnVal = fc.showOpenDialog(Main.getInstance());
	    File target = fc.getSelectedFile();
	    if (returnVal == JFileChooser.APPROVE_OPTION) {
		try {
		    final BufferedWriter out2 = new BufferedWriter(new FileWriter(target));
		    out2.write(text);
		    out2.close();
		} catch (IOException e) {
		    throw new RuntimeException("Could not store to file " + target.getAbsolutePath() + ".");
		}
	    }
	}
	
	return smtFile;
    }


    /** Read the input until end of file and return contents in a
     * single string containing all line breaks. */
    static String read(InputStream in) throws IOException {
	BufferedReader reader = new BufferedReader(new InputStreamReader(in));
	StringBuffer sb = new StringBuffer();
	int x = reader.read();
	while (x > -1) {
	    sb.append((char) x);
	    x = reader.read();
	}
	return sb.toString();
    }

    /**
     * Run this solver on a goal.
     * @param goal The goal that should be proven.
     * @param timeout The maximum time, that should be used for proving.
     * 		If it takes longer, UNKNOWN is returned.
     * @param services the service object belonging to this goal.
     * @throws IOException if the external prover could not be found, executed or if the SMT translation
     * could not be written to a file
     */ 
    public final SMTSolverResult run(Goal goal, int timeout, Services services) throws IOException {
	SMTSolverResult toReturn;
	SMTTranslator trans = this.getTranslator(services);
	try {		
	    
	instantiateTaclets(goal, trans);
	}catch(IllegalFormulaException e){
	    logger.error(e.getMessage());
	}
	  
	try{
	    String s = trans.translate(goal.sequent(), services).toString();
	    saveTacletTranslation(trans);
	    toReturn = this.run(s, timeout, services);
    	} catch (IllegalFormulaException e) {
	    toReturn = SMTSolverResult.NO_IDEA;
	    logger.debug("The formula could not be translated.", e);
	    //throw new RuntimeException("The formula could not be translated.\n" + e.getMessage());
	}
    	goal.node().addSMTandFPData(toReturn);
    	
       	return toReturn;
    }
    
    
    
    public Process run(Goal goal, Services services) throws IOException,IllegalFormulaException{
	Process toReturn;
	
	


	
	SMTTranslator trans = this.getTranslator(services);
	
	instantiateTaclets(goal, trans);

	String formula = trans.translate(goal.sequent(), services).toString();

	saveTacletTranslation(trans);
	

	
	final File loc;
	try {
	    //store the translation to a file                                
	    loc = this.storeToFile(formula);
	} catch (IOException e) {
	    logger.error("The file with the formula could not be written.", e);
	    final IOException io = new IOException("Could not create or write the input file " +
		    "for the external prover. Received error message:\n" + e.getMessage());
	    io.initCause(e);
	    throw io;
	} 
	
	

	//get the commands for execution
	String execCommand = this.getFinalExecutionCommand(loc.getAbsolutePath(), formula);

	
	try {
	    //execute the external solver
	    toReturn = Runtime.getRuntime().exec(execCommand);
	    } catch (IOException e) {
		    String cmdStr = execCommand;

		    IOException ioe = new IOException("Invocation of decision procedure\n\t\t" +
			    this.name() + "\n with command \n\t\t" + cmdStr + "\n" +  
			    "failed. The most common (but not all) reasons for this error are:\n" +
			    "\n 1. the directory where you put the executable of the decision procedure is not in your PATH.\n " +
			    "\t    Solution: Add the directory to your PATH environment variable." +
			    "\n 2. we expect a different name than your executable " +
			    "(prior to KeY 1.5 and later we expected 'Simplify' instead of 'simplify')" +
			    "\n\t Solution: Change the name to " + (execCommand != null ? 
			        	execCommand : "expected name") +
			    "\n 3. you have not the permission to execute the decision procedure." +
			    "\n\t Solution: *nix-like systems: try 'chmod u+x <path_to_executable>/<executable_filename>" +
			    "\n 4. you use a too new or too old version of the decision procedure and the command " +
			        "line parameters changed." +
			    "\n\t Solution: Install a supported version (see http://www.key-project.org)\n" +
			    "\n Original Error-Message: " + e.getMessage());
		    ioe.initCause(e);
		    throw ioe;
		}

	 
	 return toReturn;
    }


    /**
     * Run the solver on a term.
     * @param t the term to be proven.
     * @param timeout the maximum time to be used for proving.
     * 		If the time elapses, UNKNOWN is returned.
     * @throws IOException if the external prover could not be found, executed or if the SMT translation
     * could not be written to a file
     */
    public final SMTSolverResult run(Term t, int timeout, Services services) throws IOException {
	assert t.sort() == Sort.FORMULA;
	SMTSolverResult toReturn;
		
	SMTTranslator trans = this.getTranslator(services);
	
	try {

	    String s = trans.translate(t, services).toString();
	    toReturn = this.run(s, timeout, services);
    	} catch (IllegalFormulaException e) {
	    throw new RuntimeException("The formula could not be translated.\n" + e.getMessage());
	}    	
    	return toReturn;
    }

    /**
     * 
     * @return the progress made on the current task.
     */
    public int getProgress() {
	if (this.execWatch == null) {
	    return 0;
	} else {
	    return this.execWatch.getProgress();
	}
    }
    
    private ExecutionWatchDog execWatch;
    
    private ArrayList<ProgressMonitor> progressMonitors = new ArrayList<ProgressMonitor>();
    
    public void addProgressMonitor(ProgressMonitor p) {
	progressMonitors.add(p);
    }
    
    public boolean removeProgressMonitor(ProgressMonitor p) {
	return progressMonitors.remove(p);
    }
    
    public void removeAllProgressMonitors() {
	progressMonitors.clear();
	
	super.removeAllProgressMonitors();
    }
    
    /**
     * run the solver on a formula.
     * @param formula The formula to be proven in syntax, this solver supports.
     * 		Ususally it is not recommended to call this directly!
     * @param timeout
     * 		The maximum time, that should be used for the proof.
     * @param services The services object to use.
     * @throws IOException if the external prover could not be found, executed or if the SMT translation
     * could not be written to a file
     */
    public final SMTSolverResult run(String formula, 
	    	                     int timeout, 
	    			     Services services) throws IOException {
	SMTSolverResult toReturn;
	
	
	final File loc;
	try {
	    //store the translation to a file                                
	    loc = this.storeToFile(formula);
	} catch (IOException e) {
	    logger.error("The file with the formula could not be written.", e);
	    final IOException io = new IOException("Could not create or write the input file " +
		    "for the external prover. Received error message:\n" + e.getMessage());
	    io.initCause(e);
	    throw io;
	} 

	//get the commands for execution
	String execCommand = this.getFinalExecutionCommand(loc.getAbsolutePath(), formula);


	try {
	    //execute the external solver
	    Process p = Runtime.getRuntime().exec(execCommand);
	    execWatch = new ExecutionWatchDog(timeout, p);
	    Timer t = new Timer();
	    t.schedule(execWatch, new Date(System.currentTimeMillis()), 300);

	    
	    boolean interruptedByWatchdog = false;
	    try {
		//wait for the SMTSolver Thread and make popagate progress
		boolean finished = false;
		synchronized (p) {
		while (!finished) {
		    if (this.toBeInterrupted) {
			this.toBeInterrupted = false;
			execWatch.interrupt();
		    }
		    try {
			p.wait(300);
			p.exitValue();
			//if the program comes here, p has been finished.
			finished = true;
		    } catch (IllegalThreadStateException e) {
			//if program comes here, p has not been finished yet.
			//update the progress.
			for (ProgressMonitor pm : this.progressMonitors) {
			    pm.setProgress(execWatch.getProgress());
			}
		    }
		}
		}
		if (execWatch.wasInterruptedByTimeout()) {
		    interruptedByWatchdog = true;
		    logger.debug(
		    "Process for smt formula proving interrupted because of timeout.");
		} else if (execWatch.wasInterruptedByUser()) {
		    interruptedByWatchdog = true;
		    logger.debug(
		    "Process for smt formula proving interrupted because of user interaction.");
		}
	    } catch (InterruptedException f) {
		logger.debug(
			"Process for smt formula proving interrupted.",
			f);
	    } finally {
		t.cancel();
		this.execWatch = null;
	    }

	    if (interruptedByWatchdog) {
		//the solving was interrupted. So return unknown
		return SMTSolverResult.NO_IDEA;
	    } else {
		//solver terminated without watchdog.
		//collect information
		InputStream in = p.getInputStream();
		String text = read(in);
		in.close();

		in = p.getErrorStream();
		String error = read(in);
		in.close();
		try {
		    toReturn = this.interpretAnswer(text, error, p.exitValue());
		} catch (IllegalArgumentException e) {
		    //the interpretation found an error.
		    throw new RuntimeException("Error while executing solver:\n" + e.getMessage());
		} finally {
		    p.destroy();
		}

	    }
	} catch (IOException e) {
	    String cmdStr = execCommand;

	    IOException ioe = new IOException("Invocation of decision procedure\n\t\t" +
		    this.name() + "\n with command \n\t\t" + cmdStr + "\n" +  
		    "failed. The most common (but not all) reasons for this error are:\n" +
		    "\n 1. the directory where you put the executable of the decision procedure is not in your PATH.\n " +
		    "\t    Solution: Add the directory to your PATH environment variable." +
		    "\n 2. we expect a different name than your executable " +
		    "(prior to KeY 1.5 and later we expected 'Simplify' instead of 'simplify')" +
		    "\n\t Solution: Change the name to " + (execCommand != null ? 
			    execCommand : "expected name") +
		    "\n 3. you have not the permission to execute the decision procedure." +
		    "\n\t Solution: *nix-like systems: try 'chmod u+x <path_to_executable>/<executable_filename>" +
		    "\n 4. you use a too new or too old version of the decision procedure and the command " +
		        "line parameters changed." +
		    "\n\t Solution: Install a supported version (see http://www.key-project.org)\n" +
		    "\n Original Error-Message: " + e.getMessage());
	    ioe.initCause(e);
	    throw ioe;
	} 

	return toReturn;
    }
    
    public String run(String formula) throws IOException{
	final File loc;
	try {
	    //store the translation to a file                                
	    loc = this.storeToFile(formula);
	} catch (IOException e) {
	    logger.error("The file with the formula could not be written.", e);
	    final IOException io = new IOException("Could not create or write the input file " +
		    "for the external prover. Received error message:\n" + e.getMessage());
	    io.initCause(e);
	    throw io;
	} 

	//get the commands for execution
	return this.getFinalExecutionCommand(loc.getAbsolutePath(), formula);
	
    }
    
    
    public String translateToCommand(Goal goal, Services services) throws IllegalFormulaException, IOException {
	
	SMTTranslator trans = this.getTranslator(services);
	instantiateTaclets(goal, trans);
	
	  
	String s = trans.translate(goal.sequent(), services).toString();
	saveTacletTranslation(trans);
	
	

	return run(s);
    	
    }
    
    
    private boolean toBeInterrupted = false;
    
    public void interrupt() {
	this.toBeInterrupted = true;
    }
    
    
    private boolean checkEnvVariable(String cmd){
	String filesep = System.getProperty("file.separator");
	String path =  System.getenv("PATH");
	String [] res = path.split(System.getProperty("path.separator"));
	for(String s : res){
	    File file = new File(s+ filesep + cmd);
	    if(file.exists()){
		return true;
	    }
	}
	
	return false;

    }
    
    /**
     * check, if this solver is installed and can be used.
     * @param recheck if false, the solver is not checked again, if a cached value for this exists.
     * @return true, if it is installed.
     */
    public boolean isInstalled(boolean recheck) {
	if (recheck | !installwaschecked) {
	    
	
	    
	    String cmd = getExecutionCommand();
	    int first = cmd.indexOf(" ");
	    if(first >= 0){
		cmd = cmd.substring(0, first);
	    }
	    
	    if(checkEnvVariable(cmd)){
		isinstalled = true;
	    } else{
		File file = new File(cmd);
		isinstalled = file.exists();
		if(isinstalled){
		    installwaschecked = true;
		    return true;
		}
	    }

	    
	    
	    /*this.inTestMode = true;
	    try {
		//This will cause an error, but no IOException, if installed.
		//avoid to call the translator. A fakeds service element will
		//cause trouble this way.
		this.run("test", 1, new Services());
		isinstalled = true;
	    } catch (IOException e2) {
//		if exception: not installed
		isinstalled = false;
	    } catch (RuntimeException e) {
		//if this exception: some problem, but not with insatllation
		isinstalled = true;
	    }
	    this.inTestMode = false;
	    installwaschecked = true;*/
	   
	}
	return isinstalled;
    }
    
    protected String getTestFile() {
	return System.getProperty("key.home")
	    + File.separator + "examples"
	    + File.separator + "_testcase"
	    + File.separator + "smt"
	    + File.separator + "ornot.key";
    }
    
    /**
     * get the hard coded execution command from this solver.
     * The filename od a problem is indicated by %f, the problem itsself with %p
     */
    public String getDefaultExecutionCommand() {
	return this.getExecutionCommand("%f", "%p");
    }
    
    
    
  
    
    public void useTaclets(boolean b){
	this.useTaclets = b;
    }
    
    private Collection<Taclet> getTaclets(Goal goal){
	
	 if(tacletsForTest != null){
	     return tacletsForTest;
	 }
	 return ProofSettings.DEFAULT_SETTINGS.getTacletTranslationSettings()
	            .initTaclets(goal.ruleAppIndex().tacletIndex());
    }
    
   
    private void saveTacletTranslation(SMTTranslator trans) {
	if (!this.inTestMode
	        && ProofSettings.DEFAULT_SETTINGS
	                .getTacletTranslationSettings().isSaveToFile()
	        && ProofSettings.DEFAULT_SETTINGS
	                .getTacletTranslationSettings().isUsingTaclets()) {

	    DefaultTacletSetTranslation translation = (DefaultTacletSetTranslation) ((AbstractSMTTranslator) trans)
		    .getTacletSetTranslation();

	    if (translation != null) {
		translation.storeToFile(ProofSettings.DEFAULT_SETTINGS
		        .getTacletTranslationSettings().getFilename());
	    }

	}
    }
    
    private void instantiateTaclets(Goal goal, SMTTranslator trans) throws IllegalFormulaException{
	ImmutableSet<Taclet> emptySet = DefaultImmutableSet.nil();
	if(!ProofSettings.DEFAULT_SETTINGS.getTacletTranslationSettings().isUsingTaclets() || !useTaclets ){
	    trans.setTacletsForAssumptions(new LinkedList<Taclet>());
	   
	}else{
	    trans.setTacletsForAssumptions(getTaclets(goal));
	}
	
	
	 
	
	
    }
    
    public void setTacletsForTest(Collection<Taclet> set){
	tacletsForTest = set;
    }
    
    public void prepareSolver(Collection<Goal> goals, Services services) {
	init();
	session = new SolverSession(goals, services);

        
    }
    
    
    @Override
    public String[] atStart() throws Exception{

	String [] result =  new String [1];
	LinkedList<String> list = new LinkedList<String>();
	Goal goal = session.nextGoal();
	if(goal != null){

	    String s = translateToCommand(goal, session.getServices()); 
	    
	    while(s.indexOf(' ')!=-1){
		int index = s.indexOf(' ');
		list.add(s.substring(0,s.indexOf(' ')));
		s = s.substring(index+1,s.length());
	    }
	    list.add(s);

	    
	}else{
	    throw new RuntimeException("This should not happen.");
	}

	return list.toArray(new String[list.size()]);
    }
    
    @Override
    public boolean atEnd(InputStream result, InputStream error, int exitStatus) throws Exception{
	
	String text = read(result);
	result.close();

	
	String err = read(error);
	error.close();
	SMTSolverResult res = interpretAnswer(text, err, exitStatus);
	if(session.currentGoal()!= null){
	   session.currentGoal().node().addSMTandFPData(res);
	   session.addResult(res,session.currentGoal());
	}
	listener.eventCycleFinished(this,res);
	
	return !session.hasNextGoal();
    }
    
    

    public int getMaxCycle() {

        return session.getGoalSize();
    }
    
    public String toString(){
	return name();
    }
    
    public String getTitle(){
	return name();
    }

    public boolean useForMultipleRule() {
        return useForMultipleRule;
    }
    

    public void useForMultipleRule(boolean b) {
	useForMultipleRule = b;
        
    }


    public void setExecutionCommand(String s) {
        
        executionCommand = s;
    }
    
    public String getExecutionCommand(){
	return executionCommand;
    }
    


    
    
}
