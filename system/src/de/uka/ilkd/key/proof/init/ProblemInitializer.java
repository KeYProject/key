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


package de.uka.ilkd.key.proof.init;

import java.io.File;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Vector;

import recoder.io.PathList;
import recoder.io.ProjectSettings;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Field;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.JavaModel;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.io.EnvInput;
import de.uka.ilkd.key.proof.io.IProofFileParser;
import de.uka.ilkd.key.proof.io.KeYFile;
import de.uka.ilkd.key.proof.io.LDTInput;
import de.uka.ilkd.key.proof.io.LDTInput.LDTInputListener;
import de.uka.ilkd.key.proof.io.RuleSource;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.proof.mgt.GlobalProofMgt;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.RuleConfig;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.ProgressMonitor;


public final class ProblemInitializer {

    
    public static interface ProblemInitializerListener{
	public void proofCreated(ProblemInitializer sender, ProofAggregate proofAggregate);
	public void progressStarted(Object sender);
	public void progressStopped(Object sender);
	public void reportStatus(Object sender, String status, int progress);
	public void reportStatus(Object sender, String status);
	public void resetStatus(Object sender);
	public void reportException(Object sender, ProofOblInput input, Exception e);
    }    
    private static InitConfig baseConfig;
 
    private final Services services;
    private final ProgressMonitor progMon;
    private final HashSet<EnvInput> alreadyParsed = new LinkedHashSet<EnvInput>();
    private final ProblemInitializerListener listener;
    private final boolean registerProof;
    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    public ProblemInitializer(ProgressMonitor mon,
	                      Services services, boolean registerProof,
	                      ProblemInitializerListener listener) {
	this.services = services;
	this.progMon = mon;
	this.listener = listener;
	this.registerProof = registerProof;
    }
  
    
    public ProblemInitializer(Profile profile) {
        assert profile != null;
        this.progMon    = null;
        this.listener   = null;
        this.registerProof = false;
        this.services   = new Services(profile);
    }
    
        
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------

    /** 
     * displays the status report in the status line
     */
    private void reportStatus(String status) {
	if(listener != null){
	    listener.reportStatus(this,status);
	}

    }

    
    /** 
     * displays the status report in the status line 
     * and the maximum used by a progress bar
     * @param status the String to be displayed in the status line
     * @param progressMax an int describing what is 100 per cent
     */
    private void reportStatus(String status, int progressMax) {
	if(listener != null){
	    listener.reportStatus(this,status,progressMax);
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
	    keyFile[i++] = new KeYFile(name, in.get(name), progMon, initConfig.getProfile());
	}

        LDTInput ldtInp = new LDTInput(keyFile, new LDTInputListener() {
	    @Override
	    public void reportStatus(String status, int progress) {
		if(listener != null){
		    listener.reportStatus(ProblemInitializer.this, status, progress);
		}		
	    }
	}, initConfig.getProfile());
	
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
	    KeYFile keyFile = new KeYFile(fileName, in.get(fileName), progMon, envInput.getProfile());
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
	if(cfile.isDirectory()) {
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
    private JavaModel createJavaModel(String javaPath,
	    			      List<File> classPath,
	    			      File bootClassPath) 
    		throws ProofInputException {
	JavaModel result;
	if(javaPath == null) {
	    result = JavaModel.NO_MODEL;
	} else if (javaPath.equals(System.getProperty("user.home"))) { 
	    throw new ProofInputException("You do not want to have "+
	    "your home directory as the program model.");
	} else { 
	    String modelTag = "KeY_" + Long.valueOf((new java.util.Date()).getTime());
	    result = new JavaModel(javaPath, 
		    		   modelTag,
		    		   classPath,
		    		   bootClassPath);
	}
	return result;
    }
         
    
    /**
     * Helper for readEnvInput().
     */
    private void readJava(EnvInput envInput, InitConfig initConfig) 
    		throws ProofInputException {
	//this method must only be called once per init config	
	assert !initConfig.getServices()
			  .getJavaInfo()
			  .rec2key()
			  .parsedSpecial();
	assert initConfig.getProofEnv().getJavaModel() == null;
	
	//read Java source and classpath settings
	envInput.setInitConfig(initConfig);
	final String javaPath = envInput.readJavaPath();
	final List<File> classPath = envInput.readClassPath();
	final File bootClassPath = envInput.readBootClassPath();
	
	//create Recoder2KeY, set classpath
	final Recoder2KeY r2k = new Recoder2KeY(initConfig.getServices(), 
                                           initConfig.namespaces());
	r2k.setClassPath(bootClassPath, classPath);

    	//read Java (at least the library classes)		
	if(javaPath != null) {
            reportStatus("Reading Java source");
            final ProjectSettings settings 
            	=  initConfig.getServices()
            	             .getJavaInfo()
            	             .getKeYProgModelInfo()
                	     .getServConf()
                	     .getProjectSettings();
            final PathList searchPathList = settings.getSearchPathList();
            if(searchPathList.find(javaPath) == null) {
                searchPathList.add(javaPath);
            }
            final String[] cus = getClasses(javaPath).toArray(new String[]{});
            r2k.readCompilationUnitsAsFiles(cus);
	} else {
            reportStatus("Reading Java libraries");	    
	    r2k.parseSpecialClasses();
	}
        initConfig.getProofEnv().setJavaModel(createJavaModel(javaPath,
        	                                              classPath,
        	                                              bootClassPath));
    }
    
    /**
     * Removes all schema variables, all generic sorts and all sort
     * depending symbols for a generic sort out of the namespaces.
     * Helper for readEnvInput().
     * 
     * See bug report #1185, #1189
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
	//System.out.println(initConfig.funcNS().hashCode() + " ---> " + newFuncNS.hashCode());
	initConfig.getServices().getNamespaces().setVariables(newVarNS);
	initConfig.getServices().getNamespaces().setSorts(newSortNS);
	initConfig.getServices().getNamespaces().setFunctions(newFuncNS);
    }
    
    
    public final void readEnvInput(EnvInput envInput,
			      InitConfig initConfig)
    		throws ProofInputException {
	if(alreadyParsed.add(envInput)){
	    // read includes
	    if(!(envInput instanceof LDTInput)) {
		readIncludes(envInput, initConfig);
	    }

	    // read envInput itself
	    reportStatus("Reading "+envInput.name(),
		    	 envInput.getNumberOfChars());
	    envInput.setInitConfig(initConfig);
	    envInput.read();

	    // reset the variables namespace
	    initConfig.namespaces().setVariables(new Namespace());
	}
    }


    private void populateNamespaces(Term term, 
	    			    NamespaceSet namespaces,
	    			    Goal rootGoal) {
	for(int i = 0; i < term.arity(); i++) {
	    populateNamespaces(term.sub(i), namespaces, rootGoal);
	}
	
	if(term.op() instanceof Function) {
	    namespaces.functions().add(term.op());
	} else if(term.op() instanceof ProgramVariable) {
	    final ProgramVariable pv = (ProgramVariable) term.op();
	    if(namespaces.programVariables().lookup(pv.name()) == null) {
		rootGoal.addProgramVariable((ProgramVariable)term.op());
	    }
	} else if(term.op() instanceof ElementaryUpdate) {
	    final ProgramVariable pv 
	    	= (ProgramVariable)((ElementaryUpdate)term.op()).lhs();
	    if(namespaces.programVariables().lookup(pv.name()) == null) {	    
		rootGoal.addProgramVariable(pv);
	    }
	} else if(term.javaBlock() != null && !term.javaBlock().isEmpty()) {
	    final ProgramElement pe = term.javaBlock().program();
	    final Services serv = rootGoal.proof().getServices();
	    final ImmutableSet<ProgramVariable> freeProgVars 
	    	= MiscTools.getLocalIns(pe, serv)
	    	           .union(MiscTools.getLocalOuts(pe, serv));
	    for(ProgramVariable pv : freeProgVars) {
		if(namespaces.programVariables().lookup(pv.name()) == null) {	    
		    rootGoal.addProgramVariable(pv);
		}		
	    }
	}
    }
    
    
    /**
     * Ensures that the passed proof's namespaces contain all functions 
     * and program variables used in its root sequent.
     */
    private void populateNamespaces(Proof proof) {
	final NamespaceSet namespaces = proof.getNamespaces();
	final Goal rootGoal = proof.openGoals().head();
	Iterator<SequentFormula> it = proof.root().sequent().iterator();
	while(it.hasNext()) {
	    SequentFormula cf = it.next();
	    populateNamespaces(cf.formula(), namespaces, rootGoal);
	}
    }
    
        
    private InitConfig determineEnvironment(ProofOblInput po, 
	    				    InitConfig initConfig) 
    		throws ProofInputException {       
	ProofEnvironment env = initConfig.getProofEnv();
	
        //TODO: what does this actually do?
        ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().updateChoices(initConfig.choiceNS(), false);
	
	//init ruleConfig
	RuleConfig ruleConfig = new RuleConfig(initConfig.getActivatedChoices());
	env.setRuleConfig(ruleConfig);
	
	//register the proof environment
	//if(main != null) {
	 if(registerProof){
	    GlobalProofMgt.getInstance().registerProofEnvironment(env);
	}
    	               	
	return initConfig;
    }


    private void setUpProofHelper(ProofOblInput problem,ProofAggregate pl, InitConfig initConfig) 
	throws ProofInputException {
	//ProofAggregate pl = problem.getPO();
	if(pl == null) {
	   throw new ProofInputException("No proof");
	}
	
        //register non-built-in rules	
        reportStatus("Registering rules");        
        initConfig.getProofEnv().registerRules(initConfig.getTaclets(), 
        				       AxiomJustification.INSTANCE);

	Proof[] proofs = pl.getProofs();
	for(int i = 0; i < proofs.length; i++) {
	    proofs[i].setNamespaces(proofs[i].getNamespaces());//TODO: refactor Proof.setNamespaces() so this becomes unnecessary
	    populateNamespaces(proofs[i]);
	}
	initConfig.getProofEnv().registerProof(problem, pl);

    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //------------------------------------------------------------------------- 
    
    /**
     * Creates an initConfig / a proof environment and reads an EnvInput into it
     */
    public InitConfig prepare(EnvInput envInput) throws ProofInputException {
	if(listener != null){
	    listener.progressStarted(this);
	}
	alreadyParsed.clear();

        //the first time, read in standard rules
	Profile profile = envInput.getProfile();
	if(baseConfig == null || profile != baseConfig.getProfile()) {            
		InitConfig newBaseConfig = new InitConfig(services);
			RuleSource tacletBase = profile.getStandardRules().getTacletBase();
			if(tacletBase != null) {
				KeYFile tacletBaseFile
				= new KeYFile("taclet base", 
						profile.getStandardRules().getTacletBase(),
						progMon,
						profile);
				readEnvInput(tacletBaseFile, newBaseConfig);
			}
			// remove traces of the generic sorts within the base configuration
			cleanupNamespaces(newBaseConfig);
			baseConfig = newBaseConfig;
	}
	return prepare(envInput, baseConfig);
	
	}
    
    public InitConfig prepare(EnvInput envInput, InitConfig referenceConfig)throws ProofInputException{
        //create initConfig
         InitConfig initConfig = referenceConfig.copy();
        
	//register built in rules
        Profile profile = envInput.getProfile();
        for(Rule r : profile.getStandardRules().getStandardBuiltInRules()) {
            initConfig.getProofEnv().registerRule(r, 
                    profile.getJustification(r));
        }

        //read Java
        readJava(envInput, initConfig);

        //register function and predicate symbols defined by Java program
        final JavaInfo javaInfo = initConfig.getServices().getJavaInfo();
        final Namespace functions 
        = initConfig.getServices().getNamespaces().functions();
        final HeapLDT heapLDT 
        = initConfig.getServices().getTypeConverter().getHeapLDT();
        assert heapLDT != null;
        if (javaInfo != null) {
            functions.add(javaInfo.getInv());
            for(KeYJavaType kjt : javaInfo.getAllKeYJavaTypes()) {
                final Type type = kjt.getJavaType();
                if(type instanceof ClassDeclaration 
                        || type instanceof InterfaceDeclaration) {
                    for(Field f : javaInfo.getAllFields((TypeDeclaration)type)) {
                        final ProgramVariable pv 
                        = (ProgramVariable)f.getProgramVariable();
                        if(pv instanceof LocationVariable) {
                            heapLDT.getFieldSymbolForPV((LocationVariable)pv, 
                                    initConfig.getServices());
                        }
                    }
                }
                for(IProgramMethod pm
                        : javaInfo.getAllProgramMethodsLocallyDeclared(kjt)) {
                    if(!(pm.isVoid() || pm.isConstructor())) {
                        functions.add(pm);
                    }
                }
            }
        } else
                throw new ProofInputException("Problem initialization without JavaInfo!");

        //read envInput
        readEnvInput(envInput, initConfig);

        //remove generic sorts defined in KeY file
        cleanupNamespaces(initConfig);

        //done
        if(listener !=null){
           listener.progressStopped(this); 
        }
	return initConfig;
    }

    
    public Proof startProver(InitConfig initConfig, ProofOblInput po, int proofNum) 
    		throws ProofInputException {
	assert initConfig != null;
	if(listener!= null){
	    listener.progressStarted(this);
	}
        try {
            //determine environment
            initConfig = determineEnvironment(po, initConfig);
           
            //read problem
    	    reportStatus("Loading problem \"" + po.name() + "\"");
    	    po.readProblem();
    	    ProofAggregate pa = po.getPO();
    	    //final work
    	    setUpProofHelper(po, pa, initConfig);

	    //done
    	    if(listener != null){
                listener.proofCreated(this, pa);
            }
          return pa.getProofs()[proofNum];
               	    
        } catch (ProofInputException e) {    
            if(listener != null){
        	listener.reportException(this, po, e);
            }
           
            throw e;            
        } finally {
            if(listener != null){
        	listener.progressStopped(this);
            }
                   
        }    
    }
    
    
    public void startProver(ProofEnvironment env, ProofOblInput po) 
    		throws ProofInputException {
	assert env.getInitConfig().getProofEnv() == env;
        startProver(env.getInitConfig(), po, 0);
    }
    
    
    public void startProver(EnvInput envInput, ProofOblInput po) 
    		throws ProofInputException {
	try {
	    InitConfig initConfig = prepare(envInput);
	    startProver(initConfig, po, 0);
	} catch(ProofInputException e) {
	    reportStatus(envInput.name() + " failed");
	    throw e;
	}
    }
    
    
    public void tryReadProof(IProofFileParser pfp, KeYUserProblemFile kupf) 
    		throws ProofInputException {
	reportStatus("Loading proof", kupf.getNumberOfChars());
	try {
	   kupf.readProof(pfp);
	}
	finally {
	   kupf.close();
	}
    }
}
