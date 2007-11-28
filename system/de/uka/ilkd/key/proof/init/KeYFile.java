// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
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
import java.util.LinkedHashMap;

import de.uka.ilkd.key.collection.ListOfString;
import de.uka.ilkd.key.gui.configuration.LibrariesSettings;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.parser.KeYLexer;
import de.uka.ilkd.key.parser.KeYParser;
import de.uka.ilkd.key.parser.ParserConfig;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.proof.CountingBufferedInputStream;
import de.uka.ilkd.key.proof.ProblemLoader;
import de.uka.ilkd.key.proof.RuleSource;
import de.uka.ilkd.key.proof.mgt.Contract;
import de.uka.ilkd.key.proof.mgt.Contractable;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ProgressMonitor;

/** represents an input from a .key file producing an environment.
 */
public class KeYFile implements EnvInput {
    
    protected String javaPath;
    private boolean javaPathAlreadyParsed=false;


    /** the RuleSource delivering the input stream for the file.
     */
    protected RuleSource file = null;

    /** maps methods to their jml specifications. */ 
    protected LinkedHashMap method2jmlspecs=null;

    
    protected InputStream input = null;

    /** the initial configuration to be used (and modified) while reading.
     */
    protected InitConfig initConfig = null;

    private String name;

    protected KeYParser problemParser=null;
    
    protected ProofSettings settings;

    /** the graphical entity to notify on the state of reading.
     */
    protected ProgressMonitor monitor;

    /** creates a new representation for a given file by indicating a name
     * and a file representing the physical source of the .key file.
     */
    public KeYFile(String name, File file) {
	this(name, RuleSource.initRuleFile(file), null);
    }

    /** creates a new representation for a given file by indicating a name
     * and a file representing the physical source of the .key file.
     * @param monitor the progress monitor to notify on the state of reading
     */
    public KeYFile(String name, File file, ProgressMonitor monitor) {
	this(name, RuleSource.initRuleFile(file), monitor);
    }

    /** creates a new representation for a given file by indicating a name
     * and a RuleSource representing the physical source of the .key file.
     * @param monitor the progress monitor to notify on the state of reading
     */
    public KeYFile(String name, RuleSource file, ProgressMonitor monitor) {
	this.file=file;
	this.name=name;
	this.monitor=monitor;
    }

    /** returns the initial configuration that is used to read and
     * that may be modified by reading.
     */
    public InitConfig getInitConfig() {
	return initConfig;
    }

    /** returns the number of chars in the .key file.
     */
    public int getNumberOfChars() {
	return file.getNumberOfChars();
    }
    

    protected InputStream getNewStream() 
    throws FileNotFoundException {
        try {
            if (input != null) input.close();
        } catch(IOException ioe) {
            System.err.println("WARNING: Cannot close stream "+file+"\n"+ioe);
        }
        if (!file.isAvailable()) {
          throw new FileNotFoundException("File/Resource " + file + " not found.");  
        } 
        input = file.getNewStream();
        return input;
    }
    

    /** reads the whole .key file and modifies the initial configuration
     * assigned to this object according to the given modification strategy. 
     * Throws an exception if no initial configuration has been set yet.
     */
    public void read(ModStrategy mod) throws ProofInputException {
	if (initConfig==null) {
	    throw new IllegalStateException("KeYFile: InitConfig not set.");
	}	
	try {
            Debug.out("Reading KeY file", file);
	    CountingBufferedInputStream cinp = 
		new CountingBufferedInputStream
		    (getNewStream(),monitor,getNumberOfChars()/100);
            
            final NamespaceSet normal = initConfig.namespaces().copy();
            final NamespaceSet schema = setupSchemaNamespace(normal);
            
            final ParserConfig normalConfig = new ParserConfig
		(initConfig.getServices(), normal);                       
            final ParserConfig schemaConfig = new ParserConfig
                (initConfig.getServices(), schema);
            
	    problemParser = new KeYParser
		(ParserMode.PROBLEM, new KeYLexer(cinp,initConfig.getServices().getExceptionHandler()), file.toString(), schemaConfig, normalConfig, initConfig.
		 getTaclet2Builder(), initConfig.getTaclets(), initConfig.getActivatedChoices());
                problemParser.problem();
            
            
            
 
	    initConfig.addCategory2DefaultChoices(problemParser.
						  getCategory2Default());	  
	    initConfig.setTaclets(problemParser.getTaclets());
	    initConfig.add(normalConfig.namespaces(), mod);
	    if (initConfig.getProofEnv()!=null) {
		initConfig.getProofEnv().addMethodContracts
		    (problemParser.getContracts(), null);
	    }
            Debug.out("Read KeY file   ", file);
	} catch (antlr.ANTLRException e) {
	    throw new ProofInputException(e);
	} catch (FileNotFoundException fnfe) {
	    throw new ProofInputException(fnfe);
        }
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

    public Includes readIncludes() throws ProofInputException{
	if(file == null) return new Includes();
	try {
	    final ParserConfig pc = new ParserConfig
		(new Services(), new NamespaceSet());
            // FIXME: there is no exception handler here, thus, when parsing errors are ecountered
	    // during collection of includes (it is enough to mispell \include) the error
	    // message is very uninformative - ProofInputException without filename, line and column
	    // numbers. Somebody please fix that. /Woj
	    problemParser = new KeYParser
		(ParserMode.PROBLEM, 
                        new KeYLexer(getNewStream(),null), file.toString(), 
		 pc, pc, null, null, null); 
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
    

    private KeYParser createDeclParser() throws FileNotFoundException {
	return new KeYParser(ParserMode.DECLARATION,
	                     new KeYLexer(getNewStream(),
                                          initConfig.getServices().getExceptionHandler()),
			     file.toString(), 
			     initConfig.getServices().copy(),
			     initConfig.namespaces().copy());
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
        
	/*
	  two namespace sets which share all namespace except the
	  variable and function namespace 	     	      
	*/
        final NamespaceSet normal = initConfig.namespaces().copy();
	final NamespaceSet schema = setupSchemaNamespace(normal);
	
 	
        final ParserConfig schemaConfig = 
	    new ParserConfig(initConfig.getServices(), schema);

        final ParserConfig normalConfig = 
	    new ParserConfig(initConfig.getServices(), normal);
	try {
	    final CountingBufferedInputStream cinp = new CountingBufferedInputStream
            (getNewStream(),monitor,getNumberOfChars()/100);
            problemParser = new KeYParser(ParserMode.PROBLEM,
                                              new KeYLexer(cinp,
                                                           initConfig.getServices().
                                                           getExceptionHandler()), 
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


    public void readProblem(ModStrategy mod) throws ProofInputException {
	readRulesAndProblem(mod);
    }


    public void setInitConfig(InitConfig conf) {
	this.initConfig=conf;
    }


    /** reads a saved proof of a .key file
     */
    public void readProof(ProblemLoader prl) throws ProofInputException {
        try {
	    problemParser.proof(prl);
        } catch(antlr.ANTLRException e) {
            throw new ProofInputException(e);
        }
    }
    
    public ProofSettings getPreferences() throws ProofInputException {
        if (settings == null) {
            if (file.isDirectory()) return null;
            try {
                problemParser = new KeYParser(ParserMode.PROBLEM,
	           new KeYLexer(getNewStream(),null), file.toString());
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

    /** returns the name of the .key file
     */
    public String name() {
	return name;
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

    public String toString() {
	return name()+" "+file.toString();
    }
    
    public boolean equals(Object o){
	if(!(o instanceof KeYFile)) return false;
	KeYFile kf = (KeYFile) o;
	if(file != null && kf.file != null){
	    return kf.file.getExternalForm().
		equals(file.getExternalForm());
	}
	return false;
    }

    public int hashCode(){
        final String externalForm = file.getExternalForm();
        if (externalForm == null)
            return -1;
	return externalForm.hashCode();
    }

    public Contractable[] getObjectOfContract() {
        return new Contractable[0];
    }

    public boolean initContract(Contract ct) {
        return false;
    }
    
    
    public String readJavaPath() throws ProofInputException {
	if (javaPathAlreadyParsed) return javaPath;	  
        try {
            problemParser = new KeYParser(ParserMode.PROBLEM,
                                          new KeYLexer(getNewStream(),null), 
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
}
