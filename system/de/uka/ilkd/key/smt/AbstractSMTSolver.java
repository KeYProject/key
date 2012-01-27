// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.smt;


import java.io.*;
import java.util.Calendar;
import java.util.Collection;
import java.util.LinkedList;
import java.util.regex.Matcher;

import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.configuration.PathConfig;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.gui.smt.SMTSettings;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.smt.SMTSolverResult.ThreeValuedTruth;
import de.uka.ilkd.key.smt.SolverSession.InternResult;
import de.uka.ilkd.key.smt.launcher.AbstractProcess;
import de.uka.ilkd.key.smt.taclettranslation.DefaultTacletSetTranslation;
import de.uka.ilkd.key.util.Debug;


public abstract class AbstractSMTSolver extends AbstractProcess implements SMTSolver {

    
    private static int fileCounter = 0;
    
    private static synchronized int getNextFileID(){
	fileCounter++;
	return fileCounter;
    }


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
    
    private SolverSession session = null;
    
    public SolverSession getSession(){return session;}
    
    private boolean useForMultipleRule = true;

    private String command;

    private String parameters;
    
    
    
    public AbstractSMTSolver(){
	//isInstalled(true);
    }


    /**
     * Get the command for executing the external prover.
     * This is a hardcoded default value. It might be overridden by user settings
     */
 
    public abstract String getDefaultCommand();
    public abstract String getDefaultParameters();
  
    public SMTTranslator getTranslator(Services services) {
	try{
	    final SMTSettings dps = ProofSettings.DEFAULT_SETTINGS.getSMTSettings();
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

    
    private String[] getFinalSolverParameters(String filename, String formula) {

	String toReturn = getParameters();
	 // replace the placeholder with filename and fomula
	
	 toReturn = toReturn.replaceAll("%f",Matcher.quoteReplacement(filename));
	 toReturn = toReturn.replaceAll("%p", formula);	
	 return toReturn.split(" ");
	
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
	final File smtFile = new File(smtFileDir, FILE_BASE_NAME +"_"+name()+"_"+"_"+getNextFileID()+"_"+ getCurrentDateString());
	
	
	smtFile.deleteOnExit();
	
	// write the content out to the created file
	//final BufferedWriter out = new BufferedWriter(new FileWriter(smtFile));
	final Writer out = new BufferedWriter(new FileWriter(smtFile));
	out.write(text);
	out.close();

	//store the text permanent to a file 
	if (!this.inTestMode && ProofSettings.DEFAULT_SETTINGS.getSMTSettings().getSaveFile() &&
		Main.getInstance() != null) {
	    String path = ProofSettings.DEFAULT_SETTINGS.getSMTSettings().getSaveToFile();
	    	path = finalizePath(path);
		try {
		    final BufferedWriter out2 = new BufferedWriter(new FileWriter(path));
		    out2.write(text);
		    out2.close();
		} catch (IOException e) {
		    throw new RuntimeException("Could not store to file " + path + ".");
		}
	   
	}
	
	return smtFile;
    }
    
    private String finalizePath(String path){
	Calendar c = Calendar.getInstance();
	String date = c.get(Calendar.YEAR)+"-"+c.get(Calendar.MONTH)+"-"+c.get(Calendar.DATE);
	String time = c.get(Calendar.HOUR_OF_DAY)+"-"+c.get(Calendar.MINUTE)+"-"+c.get(Calendar.SECOND);
	
        path = path.replaceAll("%d", date);
        path = path.replaceAll("%s", this.getTitle());
        path = path.replaceAll("%t", time);
        path = path.replaceAll("%i", Integer.toString(AbstractSMTSolver.getNextFileID()));
        return path;
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


    
    private String[] translateToCommand(String formula, Services services) throws IOException{
	final File loc;
	try {
	    //store the translation to a file                                
	    loc = this.storeToFile(formula);
	} catch (IOException e) {
	    Debug.log4jError("The file with the formula could not be written." + e, AbstractSMTSolver.class.getName());
	    final IOException io = new IOException("Could not create or write the input file " +
		    "for the external prover. Received error message:\n" + e.getMessage());
	    io.initCause(e);
	    throw io;
	} 
	
	String pars [] = this.getFinalSolverParameters(loc.getAbsolutePath(), formula);
	String result [] = new String[pars.length+1];
	for(int i=0; i < result.length; i++){
	result[i] = i==0? getCommand() : pars[i-1];
	}


	//get the commands for execution
	return result;
	
    }
    

    private String[] translateToCommand(Term term, Services services) throws IllegalFormulaException, IOException {
	
	SMTTranslator trans = this.getTranslator(services);
	instantiateTaclets(trans);
	
 
	String formula = trans.translateProblem(term, services).toString();

	saveTacletTranslation(trans);
	
	return translateToCommand(formula, services);
    }
    

    

    
    private static boolean checkEnvVariable(String cmd){
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
    
    
    public static boolean isInstalled(String cmd){
	    
    
	    if(checkEnvVariable(cmd)){
		return true;
	    } else{
		File file = new File(cmd);
		return file.exists();
		
	    }
    }
    
    /**
     * check, if this solver is installed and can be used.
     * @param recheck if false, the solver is not checked again, if a cached value for this exists.
     * @return true, if it is installed.
     */
    public boolean isInstalled(boolean recheck) {
	if (recheck | !installwaschecked) {
	    String cmd = getCommand();
	    isinstalled = isInstalled(cmd); 
	    if(isinstalled){
		 installwaschecked = true;		      
	    }

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
    

    
    
    
  
    
    public void useTaclets(boolean b){
	this.useTaclets = b;
    }
   

    
    
    private Collection<Taclet> getTaclets(){
	 
	 if(tacletsForTest != null){
	     return tacletsForTest;
	 }
	 return session.getTaclets();
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
		String path = ProofSettings.DEFAULT_SETTINGS
	        .getTacletTranslationSettings().getFilename();
		path = finalizePath(path);
		translation.storeToFile(path);
	    }
	}
    }
    
    private void instantiateTaclets(SMTTranslator trans) throws IllegalFormulaException{
	if (!ProofSettings.DEFAULT_SETTINGS.getTacletTranslationSettings().isUsingTaclets() || !useTaclets ){
	    trans.setTacletsForAssumptions(new LinkedList<Taclet>());	   
	} else {
	    trans.setTacletsForAssumptions(getTaclets());
	}
    }
    
    public void setTacletsForTest(Collection<Taclet> set){
	tacletsForTest = set;
    }
    
    public void prepareSolver(LinkedList<InternResult> terms, Services services, Collection<Taclet> taclets) {
	init();
	session = new SolverSession(terms, services, taclets);
    }
    
    
    @Override
    public String[] atStart() throws Exception{
	String  result []= new String[0];
	InternResult term = session.nextTerm();
	//session.addResult(SMTSolverResult.createUnknownResult("",name()),session.currentTerm());
	if(term != null){
	    
	    if(term.getFormula() != null){
		result = translateToCommand(term.getFormula(), session.getServices());
	    }else{
		result = translateToCommand(term.getRealTerm(), session.getServices()); 
	    }
	     
	    


	    
	}

	return result;
    }
    
    @Override
    public boolean atEnd(InputStream result, InputStream error, int exitStatus) throws Exception{
	
	String text = read(result);
	result.close();

	
	String err = read(error);
	error.close();
	SMTSolverResult res = interpretAnswer(text, err, exitStatus);
	
	if(session.currentTerm()!= null){
	     
	   session.currentTerm().setResult(res);
	   if(res.isValid() == ThreeValuedTruth.TRUE){
	       session.incrementSolved();
	   }
	   
	
	}
	listener.eventCycleFinished(this,res);
	
	
	return !session.hasNextTerm();
    }
    
    public String getInfo() {
        return "";
    }
    
    public boolean wasSuccessful() {
 
        return session.getTermSize() == session.getSolved();
    }
    

    public int getMaxCycle() {

        return session.getTermSize();
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

    public void setCommand(String command){
	this.command = command;
    }
    
    public void setParameters(String parameters){
	this.parameters = parameters;
    }

    public String getCommand() {
	if(command == null){
	    return getDefaultCommand();
	}
	return command;
    }
    
    public String getParameters() {
	if(parameters == null){
	    return getDefaultParameters();
	}
	return parameters;
    }

    


    
    
}
