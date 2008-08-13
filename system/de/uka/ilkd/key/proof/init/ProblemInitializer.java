// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
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
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Vector;
import java.util.Map.Entry;

import recoder.io.PathList;
import recoder.io.ProjectSettings;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.collection.ListOfString;
import de.uka.ilkd.key.gui.IMain;
import de.uka.ilkd.key.gui.MethodCallInfo;
import de.uka.ilkd.key.gui.configuration.LibrariesSettings;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.CompilationUnit;
import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.IteratorOfConstrainedFormula;
import de.uka.ilkd.key.logic.IteratorOfNamed;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortDefiningSymbols;
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
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.util.ProgressMonitor;


public class ProblemInitializer {
    
    private static JavaModel lastModel;
    private static InitConfig lastBaseConfig;
 
    private final IMain main;
    private final Profile profile;
    private final Services services;
    private final UpdateSimplifier simplifier;
    
    private final ProgressMonitor pm;
    
    private final HashSet alreadyParsed = new LinkedHashSet();
    
    
    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    public ProblemInitializer(IMain main) {
        this.main       = main;
        this.pm         = main == null ? null : main.getProgressMonitor();
        this.profile    = main.mediator().getProfile();
        this.services   = new Services(main.mediator().getExceptionHandler());
        this.simplifier = ProofSettings.DEFAULT_SETTINGS
                .getSimultaneousUpdateSimplifierSettings().getSimplifier();
    }
  
    
    public ProblemInitializer(Profile profile) {
	assert profile != null;
	this.main       = null;
        this.pm         = null;
        this.profile    = profile;
        this.services   = new Services();
        this.simplifier = ProofSettings.DEFAULT_SETTINGS
                .getSimultaneousUpdateSimplifierSettings().getSimplifier();
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
     * Delayed setup of symbols defined by sorts (e.g. functions for
     * collection sorts). This may not have been done for previously
     * defined sorts, as the integer sort was not available.
     */
    private void setUpSorts(InitConfig initConfig) {
	IteratorOfNamed it = initConfig.sortNS().allElements().iterator();
        while(it.hasNext()) {
            Sort sort = (Sort)it.next ();
            if(sort instanceof SortDefiningSymbols) {
                ((SortDefiningSymbols)sort).addDefinedSymbols (initConfig.funcNS(),
                                                               initConfig.sortNS());
            }
        }
    }
    
    
    /**
     * Helper for readIncludes().
     */
    private void readLDTIncludes(Includes in, 
				 InitConfig initConfig, 
				 boolean readLibraries) 
    		throws ProofInputException {
	//avoid infinite recursion
	if(in.getLDTIncludes().isEmpty()) {
	    return;
	}
	
	//collect all ldt includes into a single LDTInput
	KeYFile[] keyFile = new KeYFile[in.getLDTIncludes().size()];
	Iterator it = in.getLDTIncludes().iterator();
	int i = 0;
	while(it.hasNext()){
	    String name = (String) it.next();
	    keyFile[i++] = new KeYFile(name, in.get(name), pm);
	}
	LDTInput ldtInp = new LDTInput(keyFile, main);
	
	//read the LDTInput
	readEnvInput(ldtInp, initConfig, readLibraries);
	
        setUpSorts(initConfig);
    }
    
    
    /**
     * Helper for readEnvInput().
     */
    private void readIncludes(EnvInput envInput, 
			      InitConfig initConfig, 
			      boolean readLibraries) 
    		throws ProofInputException {
	envInput.setInitConfig(initConfig);
	Includes in = envInput.readIncludes();
			
	//read LDT includes
	readLDTIncludes(in, initConfig, readLibraries);
	
	//read normal includes
	Iterator it = in.getIncludes().iterator();
	while(it.hasNext()){
	    String fileName = (String) it.next();
	    KeYFile keyFile = new KeYFile(fileName, in.get(fileName), pm);
	    readEnvInput(keyFile, initConfig, readLibraries);
	}
    }
    
    
    /** 
     * Helper for readEnvInput().
     */
    private void readLibraries(EnvInput envInput, InitConfig initConfig) 
            throws ProofInputException {
        reportStatus("Loading Libraries");
        
        HashMap libraries = envInput.readLibrariesSettings().getLibraries();
        if (libraries.size()==0)
            return;
        String path = LibrariesSettings.getLibrariesPath();
        Iterator it = libraries.entrySet().iterator();
        while (it.hasNext()){
            final Entry entry = (Entry) it.next();
            final String fileName = (String) entry.getKey();
            final Boolean  sel =  (Boolean) entry.getValue();
            if (sel.booleanValue()) {
                RuleSource rs;
                if (!fileName.startsWith(File.separator)) {
                    rs = RuleSource.initRuleFile(path+fileName);
                } else {
                    rs = RuleSource.initRuleFile(new File(fileName));
                }
                KeYFile keyFile = new KeYFile(fileName, rs, pm);
                readEnvInput(keyFile, initConfig, true);
            }
        }
        reportReady();
    }
    
        
    /**
     * get a vector of Strings containing all .java file names 
     * in the cfile directory.
     * Helper for readJava().
     */
    private Vector getClasses(String f) throws ProofInputException  {
	File cfile = new File(f);
	Vector v=new Vector();
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
	    String modelTag = "KeY_"+new Long((new java.util.Date()).getTime());
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
                initConfig.getProofEnv().setJavaModel(JavaModel.NO_MODEL);
            } else {                 
                String[] cus = (String[]) getClasses(javaPath).toArray(new String[]{});
                CompilationUnit[] compUnits = r2k.readCompilationUnitsAsFiles(cus);
                initConfig.getServices().getJavaInfo().setJavaSourcePath(javaPath);               

                //checkin Java model to CVS
                reportStatus("Checking Java model");
                JavaModel jmodel = getJavaModel(javaPath);
                initConfig.getProofEnv().setJavaModel(jmodel);
            }
                       
            reportReady();
            
            setUpSorts(initConfig);
	} else {
	    initConfig.getProofEnv().setJavaModel(JavaModel.NO_MODEL);
	}
    }
    
    
    private void readEnvInput(EnvInput envInput, 
			      InitConfig initConfig, 
			      boolean readLibraries) 
    		throws ProofInputException {
	if(alreadyParsed.add(envInput)){
	    //read includes
	    readIncludes(envInput, initConfig, readLibraries);
	    	    
	    //read Java
//	    readJava(envInput, initConfig);
	    
	    //read libraries
	    if(readLibraries) {
	    	readLibraries(envInput, initConfig);
	    }
	    
            //read Java
            readJava(envInput, initConfig);	
            
	    //read envInput itself
	    reportStatus("Reading "+envInput.name(), 
		    	 envInput.getNumberOfChars());
//	    System.out.println("Reading envInput: " + envInput.name());
	    envInput.setInitConfig(initConfig);
	    envInput.read(ModStrategy.NO_VARS_GENSORTS);//envInput.read(ModStrategy.NO_VARS_FUNCS_GENSORTS);	    
	    reportReady();
	    
	    setUpSorts(initConfig);
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
	
	//possibly reuse an existing proof environment
	if(main != null && po.askUserForEnvironment()) {
    	    ProofEnvironment envChosen = 
    	    GlobalProofMgt.getInstance().getProofEnvironment(
    						env.getJavaModel(), 
    						env.getRuleConfig());
        	
            if(envChosen != null) {
        	assert envChosen.getInitConfig().getProofEnv() == envChosen;
        	return envChosen.getInitConfig();
            } 
	}
	
	
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
	    proofs[i].setSimplifier(simplifier);
	    proofs[i].setNamespaces(proofs[i].getNamespaces());//TODO: refactor Proof.setNamespaces() so this becomes unnecessary
	    populateNamespaces(proofs[i]);
	}
	initConfig.getProofEnv().registerProof(problem, pl);
	if (main != null) {
            main.addProblem(pl);
        }
	GlobalProofMgt.getInstance().tryReuse(pl);	
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
    	    	readEnvInput(tacletBaseFile, lastBaseConfig, false);
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
	readEnvInput(envInput, initConfig, true);
	
	startInterface();	
	return initConfig;
    }

    
    public void startProver(InitConfig initConfig, ProofOblInput po) 
    		throws ProofInputException {
	assert initConfig != null;
	stopInterface();
	/*Setting this flag to false tells KeY to store Names in namespaces using strong references.
	 * So they are not garbage collected, while the namespace exists. If you have
	 * a better place for this statement without introducing memory leaks then refactor this code. */
	Namespace.storeAsWeak = false;
        
        try {
            //determine environment
            initConfig = determineEnvironment(po, initConfig);
           
            //read problem
    	    reportStatus("Loading problem \""+po.name()+"\"");
    	    po.readProblem(ModStrategy.NO_FUNCS);
    	    reportReady();
    	    
    	    //final work
    	    setUpProofHelper(po, initConfig);
        } catch (ProofInputException e) {           
            reportStatus(po.name() + " failed");
            throw e;            
        } finally {
            startInterface();
        }
        /*After creating the proof environment and loading of the problem we use
         * weak references to store newly created names as they become obsolete when
         * parts of a proof become pruned. */
        Namespace.storeAsWeak = true;
        if(MethodCallInfo.MethodCallCounterOn){
            MethodCallInfo.Local.reset();
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
