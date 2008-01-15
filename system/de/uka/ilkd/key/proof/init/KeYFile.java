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
import java.io.IOException;
import java.io.InputStream;

import de.uka.ilkd.key.collection.ListOfString;
import de.uka.ilkd.key.gui.configuration.LibrariesSettings;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.recoderext.RecoderModelTransformer;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.parser.KeYLexer;
import de.uka.ilkd.key.parser.KeYParser;
import de.uka.ilkd.key.parser.ParserConfig;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.proof.CountingBufferedInputStream;
import de.uka.ilkd.key.proof.RuleSource;
import de.uka.ilkd.key.rule.SetOfTaclet;
import de.uka.ilkd.key.speclang.SLEnvInput;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ProgressMonitor;


/** 
 * Represents an input from a .key file producing an environment.
 */
public class KeYFile implements EnvInput {
    
    private final String name;
    
    /** the RuleSource delivering the input stream for the file.
     */
    protected final RuleSource file;
   
    /** the graphical entity to notify on the state of reading.
     */
    protected final ProgressMonitor monitor;
    
    /**
     * for disabling the parsing of specifications (e.g. when running tests)
     */ 
    private final boolean parseSpecs;
    
    private String javaPath;
    private boolean javaPathAlreadyParsed=false;

    private ProofSettings settings;
    
    private InputStream input;
    
    protected InitConfig initConfig;
    
    private boolean chooseContract = false;
    
    
    
    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    /** creates a new representation for a given file by indicating a name
     * and a RuleSource representing the physical source of the .key file.
     */
    public KeYFile(String name, 
                   RuleSource file, 
                   ProgressMonitor monitor, 
                   boolean parseSpecs) {
        assert name != null;
        assert file != null;
        this.name = name;
        this.file = file;
        this.monitor = monitor;
        this.parseSpecs = parseSpecs;        
    }

        
    /** creates a new representation for a given file by indicating a name
     * and a file representing the physical source of the .key file.
     */
    public KeYFile(String name, 
                   File file, 
                   ProgressMonitor monitor, 
                   boolean parseSpecs) {
	this(name, RuleSource.initRuleFile(file), monitor, parseSpecs);
    }
    

    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private KeYParser createDeclParser() throws FileNotFoundException {
        return new KeYParser(ParserMode.DECLARATION,
                             new KeYLexer(getNewStream(),
                                          initConfig.getServices().getExceptionHandler()),
                             file.toString(), 
                             initConfig.getServices().copy(),
                             initConfig.namespaces().copy());
    }


    protected InputStream getNewStream() throws FileNotFoundException {
        close();
        if (!file.isAvailable()) {
            throw new FileNotFoundException("File/Resource " + file + " not found.");  
        } 
        input = file.getNewStream();
        return input;
    }
    
    
    protected ProofSettings getPreferences() throws ProofInputException {
        if (settings == null) {
            if (file.isDirectory()) {
                return null;
            }
            try {
                KeYParser problemParser 
                    = new KeYParser(ParserMode.PROBLEM,
                                    new KeYLexer(getNewStream(), null), 
                                    file.toString());
                settings = new ProofSettings(ProofSettings.DEFAULT_SETTINGS);
                settings.setProfile(ProofSettings.DEFAULT_SETTINGS.getProfile());
                settings.loadSettingsFromString(problemParser.preferences());
            } catch (antlr.ANTLRException e) {
                throw new ProofInputException(e);
            } catch (FileNotFoundException fnfe) {
                throw new ProofInputException(fnfe);
            } catch (de.uka.ilkd.key.util.ExceptionHandlerException ehe) {
                throw new ProofInputException(ehe.getCause().getMessage());
            }
        }
        return settings;
    }


    /**
     * when reading in rules modal schema operators and schemavariables are
     * added to the namespace, but shall not occur in the normal function 
     * namespaces. Therefore we take the given namespaces and use copies of 
     * the normal function and variables namespace 
     * TODO: extend the normal namespace by a generic sort and schema function
     * namespace and get rid of the schemaConfig...
     * @param normal the Namespace containing the concrete symbols 
     * @return namespace for reading in rules etc.
     */
    protected NamespaceSet setupSchemaNamespace(final NamespaceSet normal) {
        return new NamespaceSet(normal.variables().copy(), 
                normal.functions().copy(),
                normal.sorts(), 
                normal.ruleSets(),
                normal.choices(),
                normal.programVariables());
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    public String name() {
        return name;
    }
    
    
    public RecoderModelTransformer getTransformer() {
        return null;
    }

    
    public int getNumberOfChars() {
	return file.getNumberOfChars();
    }
    
    
    public void setInitConfig(InitConfig conf) {
        this.initConfig=conf;
    }


    public Includes readIncludes() throws ProofInputException{
        try {
            ParserConfig pc = new ParserConfig
                (new Services(), 
                 new NamespaceSet());
            // FIXME: there is no exception handler here, thus, when parsing errors are ecountered
            // during collection of includes (it is enough to mispell \include) the error
            // message is very uninformative - ProofInputException without filename, line and column
            // numbers. Somebody please fix that. /Woj
            KeYParser problemParser = new KeYParser(ParserMode.PROBLEM, 
                                                    new KeYLexer(getNewStream(),
                                                                 null), 
                                                    file.toString(), 
                                                    pc, 
                                                    pc, 
                                                    null, 
                                                    null, 
                                                    null); 
            problemParser.parseIncludes(); 
            return problemParser.getIncludes();
        } catch (antlr.ANTLRException e) {
            throw new ProofInputException(e);
        } catch (FileNotFoundException fnfe) {
            throw new ProofInputException(fnfe);
        } catch(de.uka.ilkd.key.util.ExceptionHandlerException ehe){
            throw new ProofInputException(ehe);
        }
    }
    
    
    public LibrariesSettings readLibrariesSettings() throws ProofInputException {
        if (initConfig==null) {
            throw new IllegalStateException("KeYFile: InitConfig not set.");
        }
        
        if (settings == null) {           
            getPreferences();            
        }
        
        LibrariesSettings result;
        if (settings == null || settings.getLibrariesSettings().emptyProperties()) {
            result = ProofSettings.DEFAULT_SETTINGS.getLibrariesSettings();
        } else {
            result = settings.getLibrariesSettings(); 
        }
        
        return result;
    }
    
    
    public String readJavaPath() throws ProofInputException {
        if (javaPathAlreadyParsed) {
            return javaPath;       
        }
        try {
            KeYParser problemParser = new KeYParser(ParserMode.PROBLEM,
                                                    new KeYLexer(getNewStream(),
                                                                 null), 
                                                    file.toString());
            
            problemParser.preferences(); // skip preferences
            
            ListOfString javaPaths = problemParser.javaSource(); 
            
            if (javaPaths == null) {
                // no java model at all
                javaPath = null;
                javaPathAlreadyParsed=true;
                return null;
            }     
            javaPath = (javaPaths.size() == 0 ? "" : javaPaths.head());
            
            if(javaPaths.size() > 1)
                Debug.fail("Don't know what to do with multiple Java paths.");            
                
            javaPathAlreadyParsed=true;
            
            if (javaPath.length() != 0) { 
                File cfile = new File(javaPath);
                if (!cfile.isAbsolute()) { // test relative pathname
                    File parent=file.file().getParentFile();
                    cfile = new File(parent,javaPath).
                    getCanonicalFile().getAbsoluteFile();
                    javaPath = cfile.getAbsolutePath();
                }
                if (!cfile.exists()) {
                    throw new ProofInputException("Declared Java source " 
                            + javaPath + " not found.");
                }                      
            }
            return javaPath;
        } catch (antlr.ANTLRException e) {
            throw new ProofInputException(e);
        } catch (IOException ioe) {
            throw new ProofInputException(ioe);
        } catch(de.uka.ilkd.key.util.ExceptionHandlerException ehe){
            ehe.printStackTrace();
            System.out.println(ehe.getCause().getMessage());
            throw new ProofInputException(ehe.getCause().getMessage());
        }
    }
    

    public void read(ModStrategy mod) throws ProofInputException {
	if (initConfig==null) {
	    throw new IllegalStateException("KeYFile: InitConfig not set.");
	}	
        
        //read .key file
	try {
            Debug.out("Reading KeY file", file);
	    CountingBufferedInputStream cinp = 
		new CountingBufferedInputStream
		    (getNewStream(),monitor,getNumberOfChars()/100);
            
	    final NamespaceSet normal = initConfig.namespaces().copy();
	    final NamespaceSet schema = setupSchemaNamespace(normal);
       
            final ParserConfig normalConfig 
                    = new ParserConfig(initConfig.getServices(), normal);                       
            final ParserConfig schemaConfig 
                    = new ParserConfig(initConfig.getServices(), schema);
            
            KeYParser problemParser 
                = new KeYParser(ParserMode.PROBLEM, 
                                new KeYLexer(cinp, 
                                             initConfig.getServices()
                                                       .getExceptionHandler()), 
                                             file.toString(), 
                                             schemaConfig, 
                                             normalConfig, 
                                             initConfig.getTaclet2Builder(), 
                                             initConfig.getTaclets(), 
                                             initConfig.getActivatedChoices()); 
            problemParser.problem(); 
	    initConfig.addCategory2DefaultChoices(problemParser.
						  getCategory2Default());
	    SetOfTaclet st = problemParser.getTaclets();
	    initConfig.setTaclets(st);
	    initConfig.add(normalConfig.namespaces(), mod);
            
	    initConfig.getServices()
                      .getSpecificationRepository()
                      .addOperationContracts(problemParser.getContracts());
            chooseContract = problemParser.getChooseContract();
            Debug.out("Read KeY file   ", file);
	} catch (antlr.ANTLRException e) {
	    throw new ProofInputException(e);
	} catch (FileNotFoundException fnfe) {
	    throw new ProofInputException(fnfe);
        }
        
        //read JML specs
        readJavaPath();
        if(parseSpecs && javaPath != null) {
            SLEnvInput slEnvInput = new SLEnvInput(javaPath);
            slEnvInput.setInitConfig(initConfig);
            slEnvInput.read(mod);
        }
    }

    
    /** reads the sorts declaration of the .key file only, 
     * modifying the sort namespace
     * of the initial configuration if allowed in the given 
     * modification strategy.
     */
    public void readSorts(ModStrategy mod) throws ProofInputException {
	try {
	    KeYParser p=createDeclParser();
	    p.parseSorts();
	    initConfig.addCategory2DefaultChoices(p.getCategory2Default());
	    initConfig.add(p.namespaces(), mod);            
	} catch (antlr.ANTLRException e) {
	    throw new ProofInputException(e);
	} catch (FileNotFoundException fnfe) {
            throw new ProofInputException(fnfe);
        }
    }
    
    
    /** reads the functions and predicates declared in the .key file only, 
     * modifying the function namespaces of the respective taclet options. 
     */
    public void readFuncAndPred(ModStrategy mod) throws ProofInputException {	
	if(file == null) return;
	try {
	    KeYParser p=createDeclParser();
	    p.parseFuncAndPred();
	    initConfig.add(p.namespaces(), mod);
	} catch (antlr.ANTLRException e) {
	    throw new ProofInputException(e);
	} catch (FileNotFoundException fnfe) {
            throw new ProofInputException(fnfe);
        }
    }

    
   /** reads the rules and problems declared in the .key file only, 
     * modifying the set of rules 
     * of the initial configuration if allowed in the given 
     * modification strategy.
     */
    public void readRulesAndProblem(ModStrategy mod) 
            throws ProofInputException {
        final NamespaceSet normal = initConfig.namespaces().copy();
	final NamespaceSet schema = setupSchemaNamespace(normal);
	
        final ParserConfig schemaConfig = 
	    new ParserConfig(initConfig.getServices(), schema);
        final ParserConfig normalConfig = 
	    new ParserConfig(initConfig.getServices(), normal);
        
	try {
	    final CountingBufferedInputStream cinp = new CountingBufferedInputStream
            (getNewStream(),monitor,getNumberOfChars()/100);
            KeYParser problemParser 
                = new KeYParser(ParserMode.PROBLEM,
                                new KeYLexer(cinp, 
                                             initConfig.getServices()
                                                       .getExceptionHandler()), 
                                file.toString(),
                                schemaConfig,
                                normalConfig,
                                initConfig.getTaclet2Builder(),
                                initConfig.getTaclets(), 
                                initConfig.getActivatedChoices());                  
            problemParser.parseTacletsAndProblem();
	    initConfig.add(normalConfig.namespaces(), mod);	   
	    initConfig.setTaclets(problemParser.getTaclets());
	} catch (antlr.ANTLRException e) {
	    throw new ProofInputException(e);
	} catch (FileNotFoundException fnfe) {
            throw new ProofInputException(fnfe);
        }
    }

    public void close() {
        try {
            if (input != null) { 
		input.close();
	    }
        } catch(IOException ioe) {
            System.err.println("WARNING: Cannot close stream "+file+"\n"+ioe);
        }
    }
    
    
    public boolean chooseContract() {
        return chooseContract;
    }

    
    public String toString() {
	return name()+" "+file.toString();
    }
    
    
    public boolean equals(Object o){
	if(!(o instanceof KeYFile)) {
            return false;
        }
	KeYFile kf = (KeYFile) o;
	 return kf.file.getExternalForm().equals(file.getExternalForm());
	
    }

    
    public int hashCode(){
        final String externalForm = file.getExternalForm();
        if (externalForm == null) {
            return -1;
        }
	return externalForm.hashCode();
    }
}
