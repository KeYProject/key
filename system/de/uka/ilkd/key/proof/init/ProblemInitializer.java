// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.init;

import java.io.File;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Vector;
import java.util.Map.Entry;

import recoder.io.PathList;
import recoder.io.ProjectSettings;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.gui.IMain;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.JavaModel;
import de.uka.ilkd.key.proof.ProblemLoader;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.RuleSource;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.proof.mgt.CvsException;
import de.uka.ilkd.key.proof.mgt.CvsRunner;
import de.uka.ilkd.key.proof.mgt.GlobalProofMgt;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.RuleConfig;
import de.uka.ilkd.key.rule.IteratorOfBuiltInRule;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.util.ProgressMonitor;


public final class ProblemInitializer {
    
    private static JavaModel lastModel;
    private static InitConfig lastBaseConfig;
 
    private final IMain main;
    private final Profile profile;
    private final Services services;
    
    private final ProgressMonitor pm;
    
    private final HashSet<EnvInput> alreadyParsed = new LinkedHashSet<EnvInput>();
    
    
    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    public ProblemInitializer(IMain main) {
        this.main       = main;
        this.pm         = main == null ? null : main.getProgressMonitor();
        this.profile    = main == null ? null : main.mediator().getProfile();
        this.services   = main == null ? null : new Services(main.mediator().getExceptionHandler());
    }
  
    
    public ProblemInitializer(Profile profile) {
	assert profile != null;
	this.main       = null;
        this.pm         = null;
        this.profile    = profile;
        this.services   = new Services();
    }
    
        
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------

    /** 
     * displays the status report in the status line
     */
    private void reportStatus(String status) {
	if (main != null) {
	    main.setStatusLine(status);	
	}
    }

    
    /** 
     * displays the status report in the status line 
     * and the maximum used by a progress bar
     * @param status the String to be displayed in the status line
     * @param progressMax an int describing what is 100 per cent
     */
    private void reportStatus(String status, int progressMax) {
	if (main != null) {
	    main.setStatusLine(status, progressMax);	
	}
    }
    

    /** 
     * displays the standard status line
     */
    private void reportReady() {
	if (main != null) {
	    main.setStandardStatusLine();
	}
    }
    
    
    private void stopInterface() {
	if(main != null) {
	    main.mediator().stopInterface(true);
	}
    }
    
    
    private void startInterface() {
	if(main != null) {
	    main.mediator().startInterface(true);
        }
    }
    
    
    /**
     * Helper for readIncludes().
     */
    private void readLDTIncludes(Includes in, 
				 InitConfig initConfig) 
    		throws ProofInputException {
	//avoid infinite recursion
	if(in.getLDTIncludes().isEmpty()) {
	    return;
	}
	
	//collect all ldt includes into a single LDTInput
	KeYFile[] keyFile = new KeYFile[in.getLDTIncludes().size()];
	
	int i = 0;
        for (String name : in.getLDTIncludes()) {
	    keyFile[i++] = new KeYFile(name, in.get(name), pm);
	}

        LDTInput ldtInp = new LDTInput(keyFile, main);
	
	//read the LDTInput
	readEnvInput(ldtInp, initConfig);
    }
    
    
    /**
     * Helper for readEnvInput().
     */
    private void readIncludes(EnvInput envInput, 
			      InitConfig initConfig) 
    		throws ProofInputException {
	envInput.setInitConfig(initConfig);
	
	Includes in = envInput.readIncludes();
        
        //read LDT includes
        readLDTIncludes(in, initConfig);
        
	//read normal includes
	for (String fileName : in.getIncludes()) {
	    KeYFile keyFile = new KeYFile(fileName, in.get(fileName), pm);
	    readEnvInput(keyFile, initConfig);
	}
    }
    
        
    /**
     * get a vector of Strings containing all .java file names 
     * in the cfile directory.
     * Helper for readJava().
     */
    private Vector<String> getClasses(String f) throws ProofInputException  {
	File cfile = new File(f);
	Vector<String> v=new Vector<String>();
	if (cfile.isDirectory()) {
	    String[] list=cfile.list();
	    // mu(2008-jan-28): if the directory is not readable for the current user
	    // list is set to null, which results in a NullPointerException.
	    if(list != null) {
	        for (int i=0; i<list.length; i++) {
	            String fullName = cfile.getPath()+File.separator+list[i];
	            File n=new File(fullName);
	            if (n.isDirectory()) {		    
	                v.addAll(getClasses(fullName));
	            } else if (list[i].endsWith(".java")) {
	                v.add(fullName);	
	            }
	        }
	    }
	    return v;
	} else {
	   throw new ProofInputException("Java model path "+f+" not found.");
	}
	
    }
    
    
    /**
     * Helper for readJava().
     */
    private JavaModel getJavaModel(String javaPath) throws ProofInputException {
        JavaModel jModel = JavaModel.NO_MODEL;
        if (javaPath != null) { 
	    String modelTag = "KeY_" + new java.util.Date().getTime();
	    jModel = new JavaModel(javaPath, modelTag);
            if (javaPath.equals(System.getProperty("user.home"))) { 
                throw new ProofInputException("You do not want to have "+
                "your home directory as the program model.");
            }
	    CvsRunner cvs = new CvsRunner();
	    try{
		boolean importOK = 
		    cvs.cvsImport(jModel.getCVSModule(), javaPath,
				  System.getProperty("user.name"),
				  modelTag);
		if (importOK && lastModel!=null && 
		    lastModel!=JavaModel.NO_MODEL && 
		    javaPath.equals(lastModel.getModelDir())) {
		    String diff = cvs.cvsDiff(jModel.getCVSModule(),
					      lastModel.getModelTag(), 
					      modelTag);
		    if (diff.length()==0) {
			jModel = lastModel;
		    }
		}
	    }catch(CvsException cvse) {
		// leave already created new Java model
		Logger.getLogger("key.proof.mgt").error("Dumping Model into CVS failed: "+cvse);
	    }
	}
	lastModel = jModel;
        return jModel;
    }
         
    
    /**
     * Helper for readEnvInput().
     */
    private void readJava(EnvInput envInput, InitConfig initConfig) 
    		throws ProofInputException {
	envInput.setInitConfig(initConfig);
	String javaPath = envInput.readJavaPath();
	List<File> classPath = envInput.readClassPath(); 
	
	if(javaPath != null) {
    	    //read Java	
            reportStatus("Reading Java model");
            ProjectSettings settings = 
                initConfig.getServices().getJavaInfo().getKeYProgModelInfo()
                	  .getServConf().getProjectSettings();
            PathList searchPathList = settings.getSearchPathList();
            
            if(searchPathList.find(javaPath) == null) {
                searchPathList.add(javaPath);
            }
            Recoder2KeY r2k = new Recoder2KeY(initConfig.getServices(), 
                                              initConfig.namespaces());
            r2k.setClassPath(classPath);
            //r2k.setKeYFile(envInput.)
            if (javaPath.length() == 0) {
                r2k.parseSpecialClasses();
                JavaModel jm = initConfig.getProofEnv().getJavaModel();
                if(jm==null){ /*This condition is bug fix. After loading java files a model is setup. 
                	However if later a .key file is loaded, then the existing model may be 
                	overwritten by NO_MODEL. This check prevents this problem. The described situation
                	may occur when using e.g. TacletLibraries from the Options menu.*/
                    initConfig.getProofEnv().setJavaModel(JavaModel.NO_MODEL);
                }
            } else {                 
                String[] cus = getClasses(javaPath).toArray(new String[]{});
                r2k.readCompilationUnitsAsFiles(cus);
                initConfig.getServices().getJavaInfo().setJavaSourcePath(javaPath);               

                //checkin Java model to CVS
                reportStatus("Checking Java model");
                JavaModel jmodel = getJavaModel(javaPath);
                initConfig.getProofEnv().setJavaModel(jmodel);
            }
                       
            reportReady();
	} else {
	    initConfig.getProofEnv().setJavaModel(JavaModel.NO_MODEL);
	}
    }
    
    
    /**
     * Removes all schema variables, all generic sorts and all sort
     * depending symbols for a generic sort out of the namespaces.
     * Helper for readEnvInput().
     */
    private void cleanupNamespaces(InitConfig initConfig) {
	Namespace newVarNS = new Namespace();	    
	Namespace newSortNS = new Namespace();
	Namespace newFuncNS = new Namespace();	    
	for(Named n : initConfig.sortNS().allElements()) {
	    if(!(n instanceof GenericSort)) {
		newSortNS.addSafely(n);
	    }	
	}
	for(Named n : initConfig.funcNS().allElements()) {
	    if(!(n instanceof SortDependingFunction 
		    && ((SortDependingFunction)n).getSortDependingOn() 
		    instanceof GenericSort)) {
		newFuncNS.addSafely(n);
	    }
	}
	initConfig.getServices().getNamespaces().setVariables(newVarNS);
	initConfig.getServices().getNamespaces().setSorts(newSortNS);
	initConfig.getServices().getNamespaces().setFunctions(newFuncNS);
    }
    
    
    private void readEnvInput(EnvInput envInput, 
			      InitConfig initConfig) 
    		throws ProofInputException {
	if(alreadyParsed.add(envInput)){
	    //read includes, java
	    if(!(envInput instanceof LDTInput)) {
		readIncludes(envInput, initConfig);
		readJava(envInput, initConfig);	
	    }
	    
	    //sanity check
	    assert initConfig.varNS().allElements().size() == 0;
	    for(Named n : initConfig.sortNS().allElements()) {
		assert n instanceof Sort && !(n instanceof GenericSort);
	    }	    
	    
	    //read envInput itself
	    reportStatus("Reading "+envInput.name(), 
		    	 envInput.getNumberOfChars());
	    envInput.setInitConfig(initConfig);
	    envInput.read();

	    //clean namespaces
	    cleanupNamespaces(initConfig);
	    	    
	    //done
	    reportReady();
	}
    }


    private void populateNamespaces(Term term, NamespaceSet namespaces) {
	for(int i = 0; i < term.arity(); i++) {
	    populateNamespaces(term.sub(i), namespaces);
	}
	
	if(term.op() instanceof Function) {
	    namespaces.functions().add(term.op());
	} else if(term.op() instanceof ProgramVariable) {
	    namespaces.programVariables().add(term.op());
	}
	
	//TODO: consider Java blocks (should not be strictly necessary 
	//for the moment, though)
    }
    
    
    /**
     * Ensures that the passed proof's namespaces contain all functions 
     * and program variables used in its root sequent.
     */
    private void populateNamespaces(Proof proof) {
	NamespaceSet namespaces = proof.getNamespaces();
	IteratorOfConstrainedFormula it = proof.root().sequent().iterator();
	while(it.hasNext()) {
	    ConstrainedFormula cf = it.next();
	    populateNamespaces(cf.formula(), namespaces);
	}
    }
    
        
    private InitConfig determineEnvironment(ProofOblInput po, 
	    				    InitConfig initConfig) 
    		throws ProofInputException {       
	ProofEnvironment env = initConfig.getProofEnv();
	
	//read activated choices
	po.readActivatedChoices();
    	initConfig.createNamespacesForActivatedChoices();
        
        //TODO: what does this actually do?
        ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().updateChoices(initConfig.choiceNS(), false);
	
	//init ruleConfig
	RuleConfig ruleConfig = new RuleConfig(initConfig.getActivatedChoices());
	env.setRuleConfig(ruleConfig);
	
	//register the proof environment
	if(main != null) {
	    GlobalProofMgt.getInstance().registerProofEnvironment(env);
	}
    	               	
	return initConfig;
    }


    private void setUpProofHelper(ProofOblInput problem, InitConfig initConfig) 
	throws ProofInputException {
	ProofAggregate pl = problem.getPO();
	if(pl == null) {
	   throw new ProofInputException("No proof");
	}
	
        //register non-built-in rules	
        reportStatus("Registering rules");        
        initConfig.getProofEnv().registerRules(initConfig.getTaclets(), 
        				       AxiomJustification.INSTANCE);
	reportReady();

	Proof[] proofs = pl.getProofs();
	for (int i=0; i < proofs.length; i++) {
	    proofs[i].setNamespaces(proofs[i].getNamespaces());//TODO: refactor Proof.setNamespaces() so this becomes unnecessary
	    populateNamespaces(proofs[i]);
	}
	initConfig.getProofEnv().registerProof(problem, pl);
	if (main != null) {
            main.addProblem(pl);
        }
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //------------------------------------------------------------------------- 
    
    /**
     * Creates an initConfig / a proof environment and reads an EnvInput into it
     */
    public InitConfig prepare(EnvInput envInput) throws ProofInputException {
	stopInterface();
	alreadyParsed.clear();

	//if the profile changed, read in standard rules
	if(lastBaseConfig == null 
	   || !lastBaseConfig.getProfile().equals(profile)) {
	    lastBaseConfig = new InitConfig(services, profile);
	    RuleSource tacletBase = profile.getStandardRules().getTacletBase();
	    if(tacletBase != null) {
    	    	KeYFile tacletBaseFile
    	    	    = new KeYFile("taclet base", 
    	    		          profile.getStandardRules().getTacletBase(),
			          pm);
    	    	readEnvInput(tacletBaseFile, lastBaseConfig);
	    }
	}
	
	//create initConfig
        InitConfig initConfig = lastBaseConfig.copy();

	//register built in rules
	final IteratorOfBuiltInRule builtInRules =
    	profile.getStandardRules().getStandardBuiltInRules().iterator();  
        while (builtInRules.hasNext()) {
            final Rule r = builtInRules.next();
    	    initConfig.getProofEnv().registerRule(r, 
    		    				  profile.getJustification(r));
        }
		
        //read envInput
        readEnvInput(envInput, initConfig);
        
	startInterface();	
	return initConfig;
    }

    
    public void startProver(InitConfig initConfig, ProofOblInput po) 
    		throws ProofInputException {
	assert initConfig != null;
	stopInterface();	
        try {
            //determine environment
            initConfig = determineEnvironment(po, initConfig);
           
            //read problem
    	    reportStatus("Loading problem \""+po.name()+"\"");
    	    po.readProblem();
    	    reportReady();
    	    
    	    //final work
    	    setUpProofHelper(po, initConfig);
        } catch (ProofInputException e) {           
            reportStatus(po.name() + " failed");
            throw e;            
        } finally {
            startInterface();            
        }    
    }
    
    
    public void startProver(ProofEnvironment env, ProofOblInput po) 
    		throws ProofInputException {
	assert env.getInitConfig().getProofEnv() == env;
        startProver(env.getInitConfig(), po);
    }
    
    
    public void startProver(EnvInput envInput, ProofOblInput po) 
    		throws ProofInputException {
	try {
	    InitConfig initConfig = prepare(envInput);
	    startProver(initConfig, po);
	} catch(ProofInputException e) {
	    reportStatus(envInput.name() + " failed");
	    throw e;
	}
    }
    
    
    public void tryReadProof(ProblemLoader prl, ProofOblInput problem) 
    		throws ProofInputException {
	if(problem instanceof KeYUserProblemFile) {
	    KeYUserProblemFile kupf = (KeYUserProblemFile)problem;
	    reportStatus("Loading proof", kupf.getNumberOfChars());
	    kupf.readProof(prl);
	}
    }
}
