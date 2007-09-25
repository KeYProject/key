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
import java.io.FileNotFoundException;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.UsedMethodContractsList;
import de.uka.ilkd.key.java.CompilationUnit;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.IteratorOfType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.ListOfType;
import de.uka.ilkd.key.java.abstraction.SLListOfType;
import de.uka.ilkd.key.java.declaration.ArrayOfTypeDeclaration;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.jml.IteratorOfJMLMethodSpec;
import de.uka.ilkd.key.jml.JMLMethodSpec;
import de.uka.ilkd.key.jml.SetOfJMLMethodSpec;
import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.parser.*;
import de.uka.ilkd.key.parser.jml.JMLSpecBuilder;
import de.uka.ilkd.key.proof.CountingBufferedInputStream;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.mgt.*;
import de.uka.ilkd.key.util.ProgressMonitor;

/** represents an input from a .key user problem file producing environment
 *  as well as a proof obligation.
 */
public class KeYUserProblemFile extends KeYFile implements ProofOblInput{

    private Term problemTerm = null;
    private String problemHeader = "";

    // if false only the specifications of Object and Datagroup are read.
    // The parsing of javacode and specifications of nonlibrary classes
    // is not affected by this flag.
    public static boolean parseLibSpecs = false;
    // for disabling the parsing of java classes and their 
    // jmlspecs when running tests
    private boolean parseJMLSpecs;


    private boolean chooseDLContract = false;
    protected boolean tacletFile = false;

    /** creates a new representation of a KeYUserFile with the given name,
     * a rule source representing the physical source of the input, and
     * a graphical representation to call back in order to report the progress
     * while reading.
     */
    public KeYUserProblemFile(String name, File file, 
			      ProgressMonitor monitor) {
	this(name, file, monitor, true);
    }

    public KeYUserProblemFile(String name, File file, 
			      ProgressMonitor monitor, boolean parseJMLSpecs) {
	super(name, file, monitor);
	this.parseJMLSpecs = parseJMLSpecs;
    }
    
    public void readHelp(ModStrategy mod, boolean problemOnly) 
	throws ProofInputException {
	if(file == null) return;
	if (initConfig==null) {
	    throw new IllegalStateException("KeYFile: InitConfig not set.");
	}
	try {
	    final CountingBufferedInputStream cinp = 
		new CountingBufferedInputStream
		    (getNewStream(),monitor,getNumberOfChars()/100);
            final DeclPicker lexer = new DeclPicker(new KeYLexer(cinp,initConfig.getServices().getExceptionHandler()));

	    /*
	      two namespace sets which share all namespace except the
	      variable namespace 	     	      
	    */
	    final NamespaceSet normal = initConfig.namespaces().copy();
	    final NamespaceSet schema = setupSchemaNamespace(normal); 		
	    final ParserConfig normalConfig 
		= new ParserConfig(initConfig.getServices(), normal);

	    final ParserConfig schemaConfig 
		= new ParserConfig(initConfig.getServices(), schema);
	    problemParser = new KeYParser(ParserMode.PROBLEM, lexer, 
					      file.toString(), 
					      schemaConfig, 
					      normalConfig,
					      initConfig.getTaclet2Builder(),
					      initConfig.getTaclets(), 
                                              initConfig.getActivatedChoices()); 
	    if (problemOnly) {
		problemTerm = problemParser.parseProblem();
	    } else {
		problemTerm = problemParser.problem();
	    }
	    String searchS = "\\problem";
	
	    if(problemTerm == null) {
	       chooseDLContract = problemParser.getChooseContract();
	       if(chooseDLContract)
  	         searchS = "\\chooseContract";
	       else {
	         if(!tacletFile) {
	           throw new ProofInputException("No \\problem or \\chooseContract in the input file!");
		 }
	       }
	    }
            problemHeader = lexer.getText();
            if(problemHeader != null && 
	       problemHeader.lastIndexOf(searchS) != -1){
		problemHeader = problemHeader.substring(
		    0, problemHeader.lastIndexOf(searchS));
	    }
	    initConfig.setTaclets(problemParser.getTaclets());
	    initConfig.add(normalConfig.namespaces(), mod);
	    
	    if(!problemOnly) {
		initConfig.getProofEnv().addMethodContracts(
			problemParser.getContracts(), problemHeader);
	    }
	} catch (antlr.ANTLRException e) {
	    throw new ProofInputException(e);
        } catch (FileNotFoundException fnfe) {
            throw new ProofInputException(fnfe);
        }
    }

    /** reads the whole .key file and modifies the initial configuration
     * assigned to this object according to the given modification strategy. 
     * Throws an exception if no initial configuration has been set yet.
     */
    public void read(ModStrategy mod) throws ProofInputException {
	readHelp(mod, false);
    }

    /** reads the the problem section of the .key file and modifies
     * the initial configuration assigned to this object according to
     * the given modification strategy.  Throws an exception if no
     * initial configuration has been set yet.
     */
    public void readProblem(ModStrategy mod) throws ProofInputException {
	readHelp(mod, true);
    }

    public ProofAggregate getPO() {

	String name = name();

        if(problemTerm == null && chooseDLContract) {
	  Iterator it = initConfig.getProofEnv().getSpecificationRepository().getSpecs();
	  ContractSet contracts = new ContractSet();
	  while (it.hasNext()) {
	    ContractSet c = (ContractSet)it.next();
	      contracts.addAll(c);
	  }
	  final ContractSet res = new ContractSet();
	  it = contracts.iterator();
	  while (it.hasNext()) {
	    Contract c = (Contract)it.next();
	    if(c instanceof DLMethodContract)
	      res.add(c);
	  }	

	  UsedMethodContractsList fr = UsedMethodContractsList.
              getInstance(Main.getInstance(false).mediator(), res);
	  fr.setVisible(true);
	  DLMethodContract c = (DLMethodContract)fr.getContract();
	  if(c == null) return null;
	  // Transform the header
	  c.setHeader(problemHeader);
	  problemHeader = c.getHeader();
	  DLHoareTriplePO poi = (DLHoareTriplePO)c.getProofOblInput(null);
	  initConfig.getServices().getNamespaces().
	     programVariables().add(c.getProgramVariables());
	  if(poi != null) {
	    problemTerm = poi.getTerm();
	    name = poi.name();
	    ProofAggregate po = ProofAggregate.createProofAggregate(
             new Proof(name, problemTerm, problemHeader,
                        initConfig.createTacletIndex(), 
                        initConfig.createBuiltInRuleIndex(),
                        initConfig.getServices(), settings), name);
	    poi.setPO(po);
	    poi.initContract(c);
    	    return po;
	  }
	  return null;
	}else{
          return ProofAggregate.createProofAggregate(
           new Proof(name, problemTerm, problemHeader,
                        initConfig.createTacletIndex(), 
                        initConfig.createBuiltInRuleIndex(),
                        initConfig.getServices(), settings), name);
	}
    }

    /** returns the <code>java.io.file</code> file encapsulated by
     * the <code>KeYUserProblemFile</code>.
     */
    public File getFile(){
	return file.file();
    }
    
    /**
     * @return Returns the problemHeader.
     */
    protected String getProblemHeader () {
        return problemHeader;
    }

    /** returns true, that is the input asks the user which
     * environment he prefers if there are multiple possibilities
     */
    public boolean askUserForEnvironment() {
	return true;
    }

    public void readSpecs(){
	    Services serv = initConfig.getServices();
	    ProgramMethod meth;
	    Iterator it;
	    if(method2jmlspecs != null && !method2jmlspecs.isEmpty()){
		it = method2jmlspecs.keySet().iterator();
		while(it.hasNext()){
		    meth = (ProgramMethod) it.next();
		    if(method2jmlspecs.get(meth) != null){
			IteratorOfJMLMethodSpec sit = 
			    ((SetOfJMLMethodSpec) 
			     method2jmlspecs.get(meth)).
			    iterator();
			while(sit.hasNext()){
			    JMLMethodSpec jmlspec = sit.next();
			    createJMLMethodContract(meth, jmlspec);
			}
		    }
		}
	    }
	    if(parseJMLSpecs){
	        final Set kjts = serv.getJavaInfo().getAllKeYJavaTypes();
	        it = kjts.iterator();
	        while(it.hasNext()){
	            final KeYJavaType kjt = (KeYJavaType) it.next();
	            if(!(kjt.getJavaType() instanceof InterfaceDeclaration
	                    || kjt.getJavaType() instanceof ClassDeclaration)){
	                continue;
	            }
	            ListOfProgramMethod ml = serv.getJavaInfo().getAllProgramMethodsLocallyDeclared(kjt);
	            IteratorOfProgramMethod mit = ml.iterator();
	            IteratorOfJMLMethodSpec sit;
	            JMLMethodSpec jmlspec;
	            while(mit.hasNext()){
	                meth = mit.next();
	                SetOfJMLMethodSpec specs = 
	                    serv.getImplementation2SpecMap().
	                    getSpecsForMethod(meth);
	                if(specs != null){
	                    sit = specs.iterator();
	                    while(sit.hasNext()){
	                        jmlspec = sit.next();
	                        createJMLMethodContract(meth, jmlspec);
	                    }
	                }
	                sit = serv.getImplementation2SpecMap().
	                getInheritedMethodSpecs(meth, kjt).iterator();
	                while(sit.hasNext()){
	                    jmlspec = sit.next();
	                    createJMLMethodContract(meth, jmlspec);
	                }
	            }
	        }
	    }
    }

    private void createJMLMethodContract(Object meth, JMLMethodSpec jmlspec){
    	Modality[] allMod = new Modality[]{Op.DIA, Op.BOX};
    	String jp = null;
	if(!jmlspec.isValid()) return;
    	try{
	    jp = readJavaPath();
    	}catch(ProofInputException e){
	    e.printStackTrace();
    	}
    	for (int i=0; i<allMod.length; i++) {	  	    
    	    OldOperationContract mct = null;
    	    if(meth instanceof ProgramMethod){
    	        KeYJavaType returnType = 
    	            ((ProgramMethod) meth).getKeYJavaType();
    	        if(returnType == null){
    	            returnType = initConfig.getServices().
    	            getJavaInfo().getKeYJavaType("void");
    	        }                
    	        mct = new JMLMethodContract(new JavaModelMethod(
    	                (ProgramMethod) meth, jp, 
    	                initConfig.getServices()), 
    	                jmlspec, allMod[i]);
    	        initConfig.getProofEnv().addMethodContract(mct);
    	    }
    	}
    }
    
    public boolean equals(Object o){
        if (o instanceof KeYUserProblemFile) {
            final KeYUserProblemFile kf = (KeYUserProblemFile) o;

            if(file != null && kf.file != null){
                return kf.file.file().getAbsolutePath().
                equals(file.file().getAbsolutePath());
            }
            if (file == null && kf.file == null){
                try{
                    return readJavaPath().equals(kf.readJavaPath());
                }catch(ProofInputException e){
                    return kf == this;
                }
            }
        }
        return false;
    }

    public int hashCode() {
        if (file == null) {
            try {
                return readJavaPath().hashCode();
            } catch (ProofInputException e) {
                return 0;
            }
        }
        return file.file().getAbsolutePath().hashCode();
    }

    protected ListOfType getTypesWithJMLSpecs(CompilationUnit[] cUnits) {
        ListOfType result = SLListOfType.EMPTY_LIST;
        final JavaInfo ji = initConfig.getServices().getJavaInfo();
        if (parseLibSpecs) {
            Set kjts = ji.getAllKeYJavaTypes();
            Iterator it = kjts.iterator();
            while (it.hasNext()) {
                KeYJavaType kjt = (KeYJavaType) it.next();
                if (kjt.getJavaType() instanceof InterfaceDeclaration
                        || kjt.getJavaType() instanceof ClassDeclaration) {
                    result = result.append(kjt.getJavaType());
                }
            }
        } else {
            for (int i = 0; i < cUnits.length; i++) {
                final ArrayOfTypeDeclaration tds = cUnits[i].getDeclarations();
                for (int j = 0; j < tds.size(); j++) {
                    final TypeDeclaration typeDecl = tds.getTypeDeclaration(j);
                    if (typeDecl instanceof InterfaceDeclaration
                            || typeDecl instanceof ClassDeclaration) {
                        result = result.append(typeDecl);
                    }
                }
            }
            result = result.append(ji.getJavaLangObject().getJavaType());
            result = result.append(ji.getKeYJavaType(
                    "org.jmlspecs.lang.JMLDataGroup").getJavaType());
            result = result.append(ji.getKeYJavaType("java.lang.Exception")
                    .getJavaType());
            result = result.append(ji.getKeYJavaType("java.lang.Throwable")
                    .getJavaType());
            result = result.append(ji.getKeYJavaType("javax.realtime.MemoryStack")
                    .getJavaType());    
            result = result.append(ji.getKeYJavaType("javax.realtime.ScopedMemory")
                    .getJavaType()); 
        }
        return result;
    }

    protected void parseJMLSpecs(ListOfType types) 
	throws ProofInputException {
	method2jmlspecs = new LinkedHashMap();
	Set builders = new LinkedHashSet();
	initConfig.createNamespacesForActivatedChoices();
	
        final IteratorOfType itt = types.iterator();
	while(itt.hasNext()){
	    TypeDeclaration t = (TypeDeclaration) itt.next();            
	    JMLSpecBuilder builder = 
		new JMLSpecBuilder(t, initConfig.getServices(), initConfig.namespaces(),
		    TermBuilder.DF, readJavaPath(), 
                    initConfig.getActivatedChoices().
                    contains(new Choice("javaSemantics", "intRules")));
	    builders.add(builder);
	}
	
        Iterator it = builders.iterator();
	while(it.hasNext()){
	    JMLSpecBuilder b = (JMLSpecBuilder) it.next();
	    b.parseModelMethodDecls();
	}
	it = builders.iterator();
	while(it.hasNext()){
	    JMLSpecBuilder b = (JMLSpecBuilder) it.next();
	    b.parseModelFieldDecls();
	}
	it = builders.iterator();
	while(it.hasNext()){
	    JMLSpecBuilder b = (JMLSpecBuilder) it.next();
	    b.parseJMLClassSpec();
	}
	it = builders.iterator();
	while(it.hasNext()){
	    JMLSpecBuilder b = (JMLSpecBuilder) it.next();
	    b.parseJMLMethodSpecs();
	    method2jmlspecs.putAll(b.getModelMethod2Specs());
	}
	initConfig.getServices().getImplementation2SpecMap().
	    createLoopAnnotations();
    }
    
    /**
     * @deprecated temporary hack
     */
    public void readJML(CompilationUnit[] compUnits)  throws ProofInputException {
	if(parseJMLSpecs){
	    parseJMLSpecs(getTypesWithJMLSpecs(compUnits));
	}
    }
    
    public void readActivatedChoices() throws ProofInputException{
	if (initConfig==null) {
	    throw new IllegalStateException("KeYFile: InitConfig not set.");
	}
	try {
            if (settings==null) getPreferences();
	    
            ParserConfig pc = new ParserConfig
		(initConfig.getServices(), 
		 initConfig.namespaces());
	    problemParser = new KeYParser
		(ParserMode.PROBLEM, new KeYLexer(getNewStream(),
		        initConfig.getServices().getExceptionHandler()), 
		        file.toString(), pc, pc, null, null, null);    
            problemParser.parseWith();            

            settings.getChoiceSettings().
             updateWith(problemParser.getActivatedChoices());           
            
            initConfig.setActivatedChoices(settings.getChoiceSettings().
                    getDefaultChoicesAsSet());

        } catch (antlr.ANTLRException e) {
	    throw new ProofInputException(e);	   
	} catch (FileNotFoundException fnfe) {
            throw new ProofInputException(fnfe);
        }
    }
    

}
