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


package de.uka.ilkd.key.java;

import java.io.*;
import java.util.*;

import recoder.ParserException;
import recoder.ProgramFactory;
import recoder.bytecode.ByteCodeParser;
import recoder.bytecode.ClassFile;
import recoder.convenience.TreeWalker;
import recoder.io.DataFileLocation;
import recoder.io.DataLocation;
import recoder.io.PropertyNames;
import recoder.java.CompilationUnit;
import recoder.java.ProgramElement;
import recoder.java.declaration.ClassInitializer;
import recoder.java.declaration.MethodDeclaration;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.parser.ParseException;
import recoder.service.ChangeHistory;
import recoder.service.CrossReferenceSourceInfo;
import recoder.service.KeYCrossReferenceSourceInfo;
import recoder.service.UnresolvedReferenceException;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.FieldSpecification;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.recoderext.*;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.util.*;
import de.uka.ilkd.key.util.LinkedHashMap;

/**
 * This class is the bridge between recoder ast data structures and KeY data
 * structures. Syntactical entities and types can be transferred from recoder to
 * KeY.
 * 
 * It manages the entire contact with the recoder framework and ensures that
 * their cross-referencing data is always uptodate. Prior to reading any source
 * code, special classes (i.e. stubs for some needed library classes) are parsed
 * in to have them available at any time.
 * 
 * To use a Recoder2KeY bridge to convert data structures you can use the
 * functions: {@link #readCompilationUnit(String)},
 * {@link #readCompilationUnitsAsFiles(String[])} or the
 * {@link #readBlock(String, Context)}-methods.
 * 
 * Results are often stored in caches.
 * 
 * It used to be monolithic but now uses separate classes for doing the actual
 * conversion and type conversion.
 * 
 * @see Recoder2KeYConverter
 * @see Recoder2KeYTypeConverter
 */

public class Recoder2KeY implements JavaReader {

    /**
     * the set of File objects that describes the classpath to be searched
     * for classes.
     * it may contain a null file which indicates that the default classes are 
     * not to be read.
     */
    private List<File> classPath;
    
    /**
     * the File object that describes the directory from which the internal
     * classes are to be read. They are read in differently - therefore the
     * second category. A null value indicates that the boot classes are to
     * be read from an internal repository.
     */
    private File bootClassPath;

    /**
     * this mapping stores the relation between recoder and KeY entities in a
     * bidirectional way.
     * 
     * It is used for syntactical structures and types.
     */
    private KeYRecoderMapping mapping;

    /**
     * Recoder's serviceConfiguration that is used throughout this process.
     */
    private KeYCrossReferenceServiceConfiguration servConf;

    /**
     * counter used to enumerate the anonymous implicit classes
     * 
     */
    private static int interactCounter = 0;

    /**
     * this flag indicates whether we are currently parsing library classes
     * (special classes)
     */
    private boolean parsingLibs = false;

    /**
     * the object that handles the transformation from recoder AST to KeY AST
     */
    private Recoder2KeYConverter converter;

    /**
     * the object that handles the transformation from recoder types to KeY
     * types
     */
    private Recoder2KeYTypeConverter typeConverter;

    /**
     * the list of classnames that contain the classes that are referenced but not 
     * defined. For those classe types a dummy stub is created at parse time.
     */
    private Collection<? extends CompilationUnit> dynamicallyCreatedCompilationUnits;
    
    private final Services services;

    /**
     * create a new Recoder2KeY transformation object.
     * 
     * The converter and type converter associated with this object will be
     * created. Several properties of the recoder framework will be set up.
     * 
     * The classpath is set to null, the mapping is retrieved from the services,
     * as well as the underlying type converter
     * 
     * @param servConf
     *            the service configuration to be used, not null
     * @param rec2key
     *            the mapping to store mapped types and mapped ASTs to, not null
     * @param nss
     *            the namespaces to work upon, not null
     * @param tc
     *            the type converter, not null
     */
    public Recoder2KeY(Services services, KeYCrossReferenceServiceConfiguration servConf, KeYRecoderMapping rec2key, NamespaceSet nss, TypeConverter tc) {
        this(services, servConf, null, rec2key, nss, tc);
    }

    /**
     * create a new Recoder2KeY transformation object.
     * 
     * The converter and type converter associated with this object will be
     * created. Several properties of the recoder framework will be set up.
     * 
     * The classpath is set to null, the mapping is retrieved from the services,
     * as well as the underlying type converter
     * 
     * @param services
     *            services to retrieve objects from, not null
     * @param nss
     *            the namespaces to work upon, not null
     */
    public Recoder2KeY(Services services, NamespaceSet nss) {
        this(services,services.getJavaInfo().getKeYProgModelInfo().getServConf(), null, services.getJavaInfo().rec2key(), nss, services.getTypeConverter());
    }

    /**
     * create a new Recoder2KeY transformation object.
     * 
     * The converter and type converter associated with this object will be
     * created. Several properties of the recoder framework will be set up.
     * 
     * @param servConf
     *            the service configuration to be used, not null
     * @param classPath
     *            the classpath to look up source files, ignored if null
     * @param rec2key
     *            the mapping to store mapped types and mapped ASTs to, not null
     * @param nss
     *            the namespaces to work upon, not null
     * @param tc
     *            the type converter, not null
     * 
     * @throws IllegalArgumentException
     *             if arguments are not valid (null e.g.)
     */
    private Recoder2KeY(Services services, KeYCrossReferenceServiceConfiguration servConf, String classPath, 
	    KeYRecoderMapping rec2key, NamespaceSet nss, TypeConverter tc) {

        if (servConf == null)
            throw new IllegalArgumentException("service configuration is null");

        if (rec2key == null)
            throw new IllegalArgumentException("rec2key mapping is null");

        if (nss == null)
            throw new IllegalArgumentException("namespaces is null");
        
        if(!(servConf.getProjectSettings().getErrorHandler() instanceof KeYRecoderExcHandler))
            throw new IllegalArgumentException("Recoder2KeY needs a KeyRecoderExcHandler as exception handler");

        this.services = services;
        this.servConf = servConf;
        this.mapping = rec2key;
        this.converter = makeConverter(services, nss);
        this.typeConverter = new Recoder2KeYTypeConverter(services, tc, nss, this);
        
        // set up recoder:
        recoder.util.Debug.setLevel(500);
        
        // do not look up classes anywhere but in the included classes 
        // or the specified classpaths
        servConf.getProjectSettings().setProperty(PropertyNames.CLASS_SEARCH_MODE, "");

    }
    
    
    
    /**
     * create the ast converter. This is overwritten in SchemaRecoder2KeY to use
     * schema-aware converters.
     * @param services 
     * 
     * @param nss the namespaces provided to the constructor 
     * 
     * @return a newley created converter
     */
    protected Recoder2KeYConverter makeConverter(Services services, NamespaceSet nss) {
        return new Recoder2KeYConverter(this, services, nss);
    }

    /**
     * return the associated converter object
     * 
     * @return not null
     */
    public Recoder2KeYConverter getConverter() {
        return converter;
    }

    /**
     * return the associated type converter object
     * 
     * @return not null
     */
    public Recoder2KeYTypeConverter getTypeConverter() {
        return typeConverter;
    }

    /**
     * set this to true before parsing special classes and to false afterwards.
     * 
     * @param v
     *            the state of the special parsing flage
     */
    private void setParsingLibs(boolean v) {
        parsingLibs = v;
    }

    /**
     * are we currently parsing library code (special classes)?
     * 
     * @return true iff currently parsing special classes.
     */
    public boolean isParsingLibs() {
        return parsingLibs;
    }

    public KeYCrossReferenceServiceConfiguration getServiceConfiguration() {
        return servConf;
    }

    public KeYRecoderMapping rec2key() {
        return mapping;
    }

    private void insertToMap(recoder.ModelElement r, ModelElement k) {
        if (r != null && k != null) {
            rec2key().put(r, k);
        } else {
            Debug.out("Rec2Key.insertToMap: Omitting entry  (r = " + r + " -> k = " + k + ")");
        }
    }

    // ----- parsing of compilation units

    /**
     * parse a list of java files and transform it to the corresponding KeY
     * entities.
     * 
     * Each element of the array is treated as a filename to read in.
     * 
     * @param cUnitStrings
     *            a list of strings, each element is interpreted as a file to be
     *            read. not null.
     * @return a new list containing the recoder compilation units corresponding
     *         to the given files.
     */

    public de.uka.ilkd.key.java.CompilationUnit[] readCompilationUnitsAsFiles(String[] cUnitStrings) {
        List<recoder.java.CompilationUnit> cUnits = recoderCompilationUnitsAsFiles(cUnitStrings);
        de.uka.ilkd.key.java.CompilationUnit[] result = new de.uka.ilkd.key.java.CompilationUnit[cUnits.size()];
        for (int i = 0, sz = cUnits.size(); i < sz; i++) {
            Debug.out("converting now " + cUnitStrings[i]);
            result[i] = getConverter().processCompilationUnit(cUnits.get(i), cUnitStrings[i]);
        }
        return result;
    }

    /**
     * parse a list of java files.
     * 
     * Each element of the array is treated as a filename to read in.
     * 
     * @param cUnitStrings
     *            a list of strings, each element is interpreted as a file to be
     *            read. not null.
     * @return a new list containing the recoder compilation units corresponding
     *         to the given files.
     */
    private List<recoder.java.CompilationUnit> recoderCompilationUnitsAsFiles(String[] cUnitStrings) {
        List<recoder.java.CompilationUnit> cUnits = new ArrayList<recoder.java.CompilationUnit>();
        parseSpecialClasses();
        try {
            for (String filename : cUnitStrings) {
                final CompilationUnit cu;
                Reader fr = null;
                try {
                    fr = new BufferedReader(new FileReader(filename));
                    cu = servConf.getProgramFactory().parseCompilationUnit(fr);
                } catch (Exception e) {
                    throw (ParseException) 
                       new ParseException("Error in file " + 
                               filename + ": " + e.getMessage()).initCause(e); 
                } finally {
                    if (fr != null) {
                	fr.close();
                    }
                }
                cu.setDataLocation(new DataFileLocation(filename));
                cUnits.add(cu);
            }
            
            final ChangeHistory changeHistory = servConf.getChangeHistory();
            for (int i = 0, sz = cUnits.size(); i < sz; i++) {
                cUnits.get(i).makeAllParentRolesValid();
                changeHistory.attached(cUnits.get(i));
            }

            if (changeHistory.needsUpdate()) {
                changeHistory.updateModel();
            }

            // transform program
            transformModel(cUnits);
        } catch (Exception ex) {
            if(ex.getCause() instanceof UnresolvedReferenceException) {
                String extraMsg = "Consider using a classpath if this is a classtype that cannot be resolved\n";
                reportError(extraMsg + ex.getCause().getMessage(), ex);
            } else {
                reportError(ex.getMessage(), ex);
            }
        }
        return cUnits;
    }
    
    /**
     * read a compilation unit, given as a string.
     * 
     * @param cUnitString
     *            a string represents a compilation unit
     * @return a KeY structured compilation unit.
     */
    public de.uka.ilkd.key.java.CompilationUnit readCompilationUnit(String cUnitString) {
        final recoder.java.CompilationUnit cc = recoderCompilationUnits(new String[] { cUnitString }).get(0);
        return (de.uka.ilkd.key.java.CompilationUnit) getConverter().process(cc);
    }

    /**
     * read a number of compilation units, each given as a string.
     * 
     * @param cUnitStrings
     *            an array of strings, each element represents a compilation
     *            unit
     * @return a list of KeY structured compilation units.
     */
    private List<recoder.java.CompilationUnit> recoderCompilationUnits(String[] cUnitStrings) {

        parseSpecialClasses();
        List<recoder.java.CompilationUnit> cUnits = new ArrayList<recoder.java.CompilationUnit>();
        int current = 0;
        Reader sr = null;
        try {
            for (int i = 0; i < cUnitStrings.length; i++) {
                current = i;
                Debug.out("Reading " + trim(cUnitStrings[i]));
                    sr = new BufferedReader(new StringReader(cUnitStrings[i]));                
                    cUnits.add(servConf.getProgramFactory().parseCompilationUnit(sr));
            }
            // run cross referencer
            final ChangeHistory changeHistory = servConf.getChangeHistory();
            for (int i = 0, sz = cUnits.size(); i < sz; i++) {
                current = i;
                cUnits.get(i).makeAllParentRolesValid();
                changeHistory.attached(cUnits.get(i));
            }

            if (changeHistory.needsUpdate()) {
                changeHistory.updateModel();
            }
            // transform program

            transformModel(cUnits);
        } catch (IOException ioe) {
            Debug.out("recoder2key: IO Error when reading" + "compilation unit " + cUnitStrings[current], ioe);
            reportError("IOError reading java program " + cUnitStrings[current] + ". May be file not found or missing permissions.", ioe);
        } catch (recoder.ParserException pe) {
            Debug.out("recoder2key: Recoder Parser Error when" + "reading a comiplation unit " + cUnitStrings[current], pe);
            if (pe.getCause() != null) {
                reportError(pe.getCause().getMessage(), pe.getCause());
            } else {
                reportError(pe.getMessage(), pe);
            }
        } finally {
            if (sr != null) {
            	try {
	            sr.close();
                } catch (IOException e) {
                    reportError("IOError reading java program " + 
                	    cUnitStrings[current] + ". May be file not found or missing permissions.", e);
                }
            }
        }
        return cUnits;
    }

    // ----- parsing libraries
    
    public void setClassPath(File bootClassPath, List<File> classPath) {
        this.classPath = classPath;
        this.bootClassPath = bootClassPath;
    }

    /**
     * get the list of names of classes that have been created dynamically due
     * to lacking definitions.
     * 
     * For all classes that are referenced but not defined, an empty dummy stub
     * is created. This method returns the list of their fully qualified class
     * names.
     * 
     * @author mu, on rb's specification ;)
     * @return an unmodifiable list of fully qualified class names
     */
    public List<String> getDynamicallyCreatedClasses() {
        List<String> ret = new ArrayList<String>();
        if(dynamicallyCreatedCompilationUnits != null) {
            for (CompilationUnit cu : dynamicallyCreatedCompilationUnits) {
                ret.add(cu.getPrimaryTypeDeclaration().getFullName());
            }
        }
        return ret;
    }
    
    /**
     * This method loads the internal classes - also called the "boot" classes.
     * 
     * If {@link #bootClassPath} is set to null, it locates java classes that
     * are stored internally within the jar-file or the binary directory. The
     * JAVALANG.TXT file lists all files to be loaded. The files are found using
     * a special {@link JavaReduxFileCollection}.
     * 
     * If, however, {@link #bootClassPath} is assigned a value, this is treated
     * as a directory (not a JAR file at the moment) and all files in this
     * directory are read in. This is done using a
     * {@link DirectoryFileCollection}.
     */
    private void parseInternalClasses(ProgramFactory pf, List<recoder.java.CompilationUnit> rcuList) 
                    throws IOException, ParseException, ParserException {
        
        FileCollection bootCollection;
        FileCollection.Walker walker = null;
        if(bootClassPath == null) {
            bootCollection = new JavaReduxFileCollection(services.getProfile());
            walker = bootCollection.createWalker(".java");
        } else {
            bootCollection = new DirectoryFileCollection(bootClassPath);
            walker = bootCollection.createWalker(new String[] {".java", ".jml"} );
        }
        
        
        while(walker.step()) {
            DataLocation loc = walker.getCurrentDataLocation();
            InputStream is = walker.openCurrent();
            Reader f = new BufferedReader(new InputStreamReader(is));
            
            try {
                recoder.java.CompilationUnit rcu = pf.parseCompilationUnit(f);
                rcu.setDataLocation(loc);
                // done by parser : rcu.makeAllParentRolesValid();
                rcuList.add(rcu);
            } catch(ParseException ex) {
                ParseException e2 = new ParseException("Error while parsing " + loc);
                e2.initCause(ex);
                throw e2;
            } catch(Exception ex){
    	        ConvertException e2 = new ConvertException("While parsing "+loc+"\n"+ex.getMessage());
                e2.initCause(ex);
                throw e2;
            } finally {        
        	    f.close();
            }
            
            
            if (Debug.ENABLE_DEBUG) {
                Debug.out("parsed: " + loc);
            }
        }
        
    }
    
    /**
     * reads compilation units that will be treated as library classes.
     * 
     * Proceed as follows:
     * 
     * <ol>
     * <li> If "classPath" is set and contains at least one entry
     * <ol>
     * <li>read every <code>.java</code> file within the entries (directories
     * or zip files)
     * <li>read every <code>.class</code> file within the entries
     * (directories or zip files)
     * </ol>
     * <li>else read a special collection of classes that is stored internally
     * </ol>
     * 
     * @author mulbrich
     * @throws ParserException
     * @throws IOException
     * @throws ParseException
     */
    private List<recoder.java.CompilationUnit> parseLibs() throws ParseException, IOException, ParserException {
        
        recoder.ProgramFactory pf = servConf.getProgramFactory();
        List<recoder.java.CompilationUnit> rcuList = new LinkedList<recoder.java.CompilationUnit>();
        List<FileCollection> sources = new ArrayList<FileCollection>();
        
        parseInternalClasses(pf, rcuList);

        if(classPath != null) {
            for(File cp : classPath) {
                if(cp.isDirectory())
                    sources.add(new DirectoryFileCollection(cp));
                else
                    sources.add(new ZipFileCollection(cp));
            }
        }

        DataLocation currentDataLocation = null;

        // -- read jml files --
        for (FileCollection fc : sources) {
            FileCollection.Walker walker = fc.createWalker(".jml");
            while(walker.step()) {
        	Reader f = null;
        	try {
                    currentDataLocation = walker.getCurrentDataLocation();
                    InputStream is = walker.openCurrent();
                    f = new BufferedReader(new InputStreamReader(is));
                    recoder.java.CompilationUnit rcu = pf.parseCompilationUnit(f);
                    rcu.setDataLocation(currentDataLocation);
                    removeCodeFromClasses(rcu, false);
                    rcuList.add(rcu);
                } catch(Exception ex) {
                    throw new ConvertException("Error while loading: " + walker.getCurrentDataLocation(), ex);
                } finally {
                    if (f != null) {
                	f.close();
                    }
                }
            }
        }

        // -- read java files --
        for (FileCollection fc : sources) {
            FileCollection.Walker walker = fc.createWalker(".java");
            while(walker.step()) {
        	Reader f = null;
        	try {
                    currentDataLocation = walker.getCurrentDataLocation();
                    InputStream is = walker.openCurrent();
                    f = new BufferedReader(new InputStreamReader(is));
                    recoder.java.CompilationUnit rcu = pf.parseCompilationUnit(f);
                    rcu.setDataLocation(currentDataLocation);
                    removeCodeFromClasses(rcu, true);
                    rcuList.add(rcu);
                } catch(Exception ex) {
                    throw new ConvertException("Error while loading: " + walker.getCurrentDataLocation(), ex);
                } finally {
                    if (f != null) {
                	f.close();
                    }
                }
            }
        }

        // -- read class files --
        ClassFileDeclarationManager manager = new ClassFileDeclarationManager(pf); 
        ByteCodeParser parser = new ByteCodeParser();
        for (FileCollection fc : sources) {
            FileCollection.Walker walker = fc.createWalker(".class");
            while(walker.step()) {
        	InputStream is = null;
        	try {
                    currentDataLocation = walker.getCurrentDataLocation();
                    is = new BufferedInputStream(walker.openCurrent());
                    ClassFile cf;
                    try {
                        cf = parser.parseClassFile(is);
                    } finally {
                        is.close();
                    }
                    manager.addClassFile(cf, currentDataLocation);
                } catch(Exception ex) {
                    throw new ConvertException("Error while loading: " + walker.getCurrentDataLocation(), ex);
                }
            }
        }
        rcuList.addAll(manager.getCompilationUnits());
        
        recoder.java.CompilationUnit rcu = pf.parseCompilationUnit(
                new StringReader("public class " +
                        JavaInfo.DEFAULT_EXECUTION_CONTEXT_CLASS + " { public static void " + JavaInfo.DEFAULT_EXECUTION_CONTEXT_METHOD + "() {}  }"));
        rcuList.add(rcu);

        return rcuList;
        
    }

    /*
     * removes code from a parsed compilation unit. This includes method bodies,
     * initial assignments, compile-time constants, static blocks.
     * 
     * This is done for classes that are read in a classpath-context. For these
     * classes only contracts (if present) are to be considered.
     * 
     * No need to inform changeHistory since the class is not yet registered.
     * Method bodies are set to null, i.e. all methods are stubs only
     * 
     * TODO remove jml-model methods (or similar) also?
     * FIXME this does not work if jml set statements are last in a method
     * TODO leave it out all together?
     */
    private void removeCodeFromClasses(CompilationUnit rcu, boolean allowed) {
        TreeWalker tw = new TreeWalker(rcu);
        
        while(tw.next()) {
            ProgramElement pe = tw.getProgramElement();
            if (pe instanceof MethodDeclaration) {
                MethodDeclaration methDecl = (MethodDeclaration) pe;
                if(!allowed && methDecl.getBody() != null) {
                    Debug.log4jWarn("Method body ("+methDecl.getName()+") should not be allowed: "+rcu.getDataLocation(),
                	            Recoder2KeY.class.getName());
                }
                methDecl.setBody(null);
            }
            /*
            // This is deactivated to allow compile time constants in declaration stub files.
            // see bug #1114 
            if (pe instanceof recoder.java.declaration.FieldSpecification) {
                recoder.java.declaration.FieldSpecification fieldSpec = 
                    (recoder.java.declaration.FieldSpecification) pe;
                if(!allowed && fieldSpec.getInitializer() != null) {
                    Debug.log4jWarn("Field initializer ("+fieldSpec.getName()+") should not be allowed: "+rcu.getDataLocation(),
                	    	    Recoder2KeY.class.getName());
                }
                fieldSpec.setInitializer(null);
            }
            */
            if (pe instanceof ClassInitializer) {
                ClassInitializer classInit = (ClassInitializer) pe;
                if(!allowed && classInit.getBody() != null) {
                    Debug.log4jWarn("There should be no class initializers: "+rcu.getDataLocation(),
                	    	    Recoder2KeY.class.getName());
                }
                classInit.setBody(null);
            }
        }
    }

    /**
     * makes sure that the special classes (library classes) have been parsed
     * in.
     * 
     * If not parsed yet, the special classes are read in and converted.
     * This method throws only runtime exceptions for historical reasons.
     */
    public void parseSpecialClasses() {
        try {
            parseLibraryClasses0();
        } catch (Exception e) {
            reportError("An error occurred while parsing the libraries", e);
        }
    }
    
    
    private void parseLibraryClasses0() throws ParseException, IOException, ParserException {
        if (mapping.parsedSpecial()) {
            return;
        }

        // go to special mode -> used by the converter!
        setParsingLibs(true);

        List<recoder.java.CompilationUnit> specialClasses = parseLibs();

//        for (recoder.java.CompilationUnit compilationUnit : specialClasses) {
//            System.out.println(compilationUnit.toSource());
//        }
        
        ChangeHistory changeHistory = servConf.getChangeHistory();
        for (int i = 0, sz = specialClasses.size(); i < sz; i++) {
            specialClasses.get(i).makeAllParentRolesValid();
            // TODO if duplicated files, take first one only!
            changeHistory.attached(specialClasses.get(i));
        }
        
        
        CrossReferenceSourceInfo sourceInfo = servConf.getCrossReferenceSourceInfo();
        assert sourceInfo instanceof KeYCrossReferenceSourceInfo :
            "SourceInfo is not of type KeYCrossReferenceSourceInfo";
        KeYCrossReferenceSourceInfo keySourceInfo = 
            (KeYCrossReferenceSourceInfo)sourceInfo;
        
        keySourceInfo.setIgnoreUnresolvedClasses(true);

        if (changeHistory.needsUpdate()) {
            changeHistory.updateModel();
        }
        
        dynamicallyCreatedCompilationUnits = keySourceInfo.getCreatedStubClasses();
        specialClasses.addAll(dynamicallyCreatedCompilationUnits);
        keySourceInfo.setIgnoreUnresolvedClasses(false);
        
        changeHistory.updateModel();

        transformModel(specialClasses);
        
//        NameInfo ni = servConf.getNameInfo();
//        System.out.println("Known types:");
//        for(ClassType ct : ni.getClassTypes()) {
//            System.out.println(ct.getFullName());
//        }
        
        // make them available to the rec2key mapping
        for(recoder.java.CompilationUnit cu : specialClasses) {
            DataLocation dl = cu.getOriginalDataLocation();
            assert dl != null : "DataLocation not set on " + cu.toSource();
            getConverter().processCompilationUnit(cu, dl.toString());
        }
        
        // tell the mapping that we have parsed the special classes
        rec2key().parsedSpecial(true);

        setParsingLibs(false);
    }

    /**
     * Transform a list of compilation units.
     * 
     * Once a compilation unit has been parsed in and prior to converting it to
     * the KeY structures, several transformations have to be performed upon it.
     * 
     * You can add your own Transformation here. Make sure it is in the correct
     * order.
     * 
     * @param cUnits
     *            a list of compilation units, not null.
     */

    protected void transformModel(List<recoder.java.CompilationUnit> cUnits) {

        RecoderModelTransformer.TransformerCache cache = new RecoderModelTransformer.TransformerCache(cUnits);
        
        ConstructorNormalformBuilder cnb; 
                
        RecoderModelTransformer[] transformer = new RecoderModelTransformer[] {
                new EnumClassBuilder(servConf, cache),
                new JMLTransformer(servConf, cache),
                new ImplicitFieldAdder(servConf, cache),
                new InstanceAllocationMethodBuilder(servConf, cache),
                cnb = new ConstructorNormalformBuilder(servConf, cache),
                new ClassPreparationMethodBuilder(servConf, cache),
                new ClassInitializeMethodBuilder(servConf, cache), 
                new PrepareObjectBuilder(servConf, cache), 
                new CreateBuilder(servConf, cache),
                new CreateObjectBuilder(servConf, cache),
                new LocalClassTransformation(servConf, cache),
                new ConstantStringExpressionEvaluator(servConf, cache)
        };

        
        final ChangeHistory cHistory = servConf.getChangeHistory();
        for (RecoderModelTransformer aTransformer : transformer) {
            if (Debug.ENABLE_DEBUG) {
                Debug.out("current transformer : " + aTransformer.toString());
            }
            aTransformer.execute();
        }
        
        converter.locClass2finalVar = cnb.getLocalClass2FinalVar();

        if (cHistory.needsUpdate()) {
            cHistory.updateModel();
        }
        
        // recoder changes the data location to some imaginary files
        // undo this by setting the original locations
        for (recoder.java.CompilationUnit cu : cUnits) {
            cu.setDataLocation(cu.getOriginalDataLocation());
        }
    }

    // ----- methods dealing with blocks.

    /**
     * wraps a RECODER StatementBlock in a method
     * 
     * it is wrapped in a method called
     * <code>&lt;virtual_method_for_parsing&gt;</code>.
     * 
     * @param block
     *            the recoder.java.StatementBlock to wrap
     * @return the enclosing recoder.java.MethodDeclaration
     */
    protected recoder.java.declaration.MethodDeclaration embedBlock(recoder.java.StatementBlock block) {

        /*
         * MethodDeclaration(modifiers,return type,Identifier, parameters,
         * throws, StatementBlock)
         */
        recoder.java.declaration.MethodDeclaration mdecl = new recoder.java.declaration.MethodDeclaration(null, null, new ImplicitIdentifier(
                "<virtual_method_for_parsing>"), null, null, block);
        mdecl.makeParentRoleValid();
        return mdecl;
    }

    /**
     * wraps a RECODER MethodDeclaration in a class
     * 
     * @param mdecl
     *            the recoder.java.declaration.MethodDeclaration to wrap
     * @param context
     *            the recoder.java.declaration.ClassDeclaration where the method
     *            has to be embedded
     * @return the enclosing recoder.java.declaration.ClassDeclaration
     */
    protected recoder.java.declaration.ClassDeclaration embedMethod(recoder.java.declaration.MethodDeclaration mdecl, Context context) {

        recoder.java.declaration.ClassDeclaration classContext = context.getClassContext();

        // add method to member declaration list
        ASTList<recoder.java.declaration.MemberDeclaration> memberList = classContext.getMembers();

        if (memberList == null) {
            memberList = new ASTArrayList<recoder.java.declaration.MemberDeclaration>(1);
            classContext.setMembers(memberList);
        }

        for (int i = 0, sz = memberList.size(); i < sz; i++) {
            if (memberList.get(i) instanceof recoder.java.declaration.MethodDeclaration) {
                recoder.java.declaration.MethodDeclaration olddecl = (recoder.java.declaration.MethodDeclaration) memberList.get(i);
                if (olddecl.getName().equals(mdecl.getName())) {
                    memberList.remove(i);
                }
            }
        }
        memberList.add(mdecl);

        // add method to class

        classContext.setProgramModelInfo(servConf.getCrossReferenceSourceInfo());
        classContext.makeParentRoleValid();
        return classContext;
    }

    /**
     * creates an empty RECODER compilation unit with a temporary name.
     * 
     * @return the new recoder.java.CompilationUnit
     */
    public Context createEmptyContext() {
        recoder.java.declaration.ClassDeclaration classContext = interactClassDecl();
        return new Context(servConf, classContext);
    }

    /**
     * create a new context with a temporary name and make a list of variables
     * visible from within. Use the default source info.
     * 
     * @param pvs
     *            a list of variables
     * @return a newly created context.
     */

    protected Context createContext(ImmutableList<ProgramVariable> pvs) {
        return createContext(pvs, servConf.getCrossReferenceSourceInfo());
    }

    /**
     * create a new Context with a temporary name and make a list of variables
     * visible from within.
     * 
     * @param vars
     *            a list of variables
     * @param csi
     *            a special source info
     * 
     * @return a newly created context.
     */
    protected Context createContext(ImmutableList<ProgramVariable> vars, recoder.service.CrossReferenceSourceInfo csi) {
        recoder.java.declaration.ClassDeclaration classContext = interactClassDecl();
        addProgramVariablesToClassContext(classContext, vars, csi);
        return new Context(servConf, classContext);
    }

    /**
     * add a list of variables to a context
     * 
     * @param classContext
     *            context to add to
     * @param vars
     *            vars to add
     */
    private void addProgramVariablesToClassContext(recoder.java.declaration.ClassDeclaration classContext, ImmutableList<ProgramVariable> vars,
            recoder.service.CrossReferenceSourceInfo csi) {

        HashMap<String, recoder.java.declaration.VariableSpecification> names2var = 
            new LinkedHashMap<String, recoder.java.declaration.VariableSpecification>();
        Iterator<ProgramVariable> it = vars.iterator();
        java.util.HashSet<String> names = new java.util.HashSet<String>();
        ASTList<recoder.java.declaration.MemberDeclaration> list = classContext.getMembers();

        // perhaps install a new list for the members of the class context
        if (list == null) {
            list = new ASTArrayList<recoder.java.declaration.MemberDeclaration>(1);
            classContext.setMembers(list);
        }

        l: while (it.hasNext()) {
            VariableSpecification keyVarSpec;
            ProgramVariable var = it.next();
            if (names.contains(var.name().toString())) {
                continue l;
            }
            names.add(var.name().toString());
            keyVarSpec = lookupVarSpec(var);
            if (keyVarSpec == null) {
                keyVarSpec = new FieldSpecification(var);
            }

            if (var.getKeYJavaType() == null) {
                throw new IllegalArgumentException("Variable " + var + " has no type");
            }

            String typeName = "";
            Type javaType = var.getKeYJavaType().getJavaType();
            if(javaType == null) continue;
            typeName = javaType.getFullName();

            recoder.java.declaration.FieldDeclaration recVar = new recoder.java.declaration.FieldDeclaration(null, name2typeReference(typeName),
                    new ExtendedIdentifier(keyVarSpec.getName()), null);

            list.add(recVar);
            classContext.makeAllParentRolesValid();
            recoder.java.declaration.VariableSpecification rvarspec = recVar.getVariables().get(0);
            names2var.put(var.name().toString(), rvarspec);

            rvarspec.setProgramModelInfo(csi);
            insertToMap(recVar.getVariables().get(0), keyVarSpec);
        }

        ((KeYCrossReferenceSourceInfo) csi).setNames2Vars(names2var);
        servConf.getChangeHistory().updateModel();
    }

    /**
     * look up in the mapping the variable specification for a program variable.
     * 
     * used by addProgramVariablesToClassContext
     */
    private VariableSpecification lookupVarSpec(ProgramVariable pv) {
        for (final Object o : mapping.elemsKeY()) {
            if ((o instanceof VariableSpecification) && ((VariableSpecification) o).getProgramVariable() == pv) {
                return (VariableSpecification) o;
            }
        }
        return null;
    }

    /**
     * given a name as string, construct a recoder type reference from it.
     * 
     * @param typeName
     *            non-null type name as string
     * @return a freshly created type reference to the given type.
     */
    private recoder.java.reference.TypeReference name2typeReference(String typeName) {
        recoder.java.reference.PackageReference pr = null;
        String baseType = TypeNameTranslator.getBaseType(typeName);
        int idx = baseType.indexOf('.');
        int lastIndex = 0;
        String anonType="";
        while (idx != -1 && baseType.charAt(lastIndex) >= 'a' 
                && baseType.charAt(lastIndex) <= 'z') {
            String s = baseType.substring(lastIndex, idx);
            pr = new recoder.java.reference.PackageReference
                    (pr, new recoder.java.Identifier(s));
            lastIndex = idx + 1;
            idx = baseType.indexOf('.', lastIndex);
        }
        baseType = anonType+baseType;
        recoder.java.Identifier typeId;
        if (baseType.charAt(0) == '<') {
            typeId = new ImplicitIdentifier(baseType.substring(lastIndex));
        } else {
            typeId = new ObjectTypeIdentifier(baseType.substring(lastIndex));
        }
        recoder.java.reference.TypeReference result =
            new recoder.java.reference.TypeReference(pr, typeId);
        result.setDimensions(TypeNameTranslator.getDimensions(typeName));
        return result;
    }

    /**
     * parses a given JavaBlock using the context to determine the right
     * references and returns a statement block of recoder.
     * 
     * @param block
     *            a String describing a java block
     * @param context
     *            recoder.java.CompilationUnit in which the block has to be
     *            interpreted
     * @return the parsed and resolved recoder statement block
     */
    recoder.java.StatementBlock recoderBlock(String block, Context context) {
        recoder.java.StatementBlock bl = null;
        parseSpecialClasses();
        Reader sr = null;
        try {
            sr = new BufferedReader(new StringReader(block));
            bl = servConf.getProgramFactory().parseStatementBlock(sr);
            bl.makeAllParentRolesValid();
            embedMethod(embedBlock(bl), context);
            context.getCompilationUnitContext().makeParentRoleValid();
            // servConf.getCrossReferenceSourceInfo().register(bl);
            // register() is deprecated. so use this instead:
            servConf.getChangeHistory().attached(bl);
            servConf.getChangeHistory().attached(context.getCompilationUnitContext());
            servConf.getChangeHistory().updateModel();
        
            // normalise constant string expressions
            List<CompilationUnit> cunits = new ArrayList<CompilationUnit>();
            cunits.add(context.getCompilationUnitContext());
            final RecoderModelTransformer.TransformerCache cache = new RecoderModelTransformer.TransformerCache(cunits);
            new ConstantStringExpressionEvaluator(servConf, cache).execute();
        } catch (de.uka.ilkd.key.util.ExceptionHandlerException e) {
            if (e.getCause() != null) {
                reportError(e.getCause().getMessage(), e.getCause());
            } else {
                reportError(e.getMessage(), e);
            }
        } catch (recoder.service.UnresolvedReferenceException e) {
            reportError("Could not resolve reference:" + e.getUnresolvedReference(), e);
        } catch (recoder.parser.ParseException e) {
            if (e.getCause() != null) {
                reportError(e.getCause().getMessage(), e.getCause());
            } else {
                reportError(e.getMessage(), e);
            }
        } catch (recoder.ModelException e) {
            if (e.getCause() != null) {
                reportError(e.getCause().getMessage(), e.getCause());
            } else {
                reportError(e.getMessage(), e);
            }
        } catch (recoder.ParserException e) {
            if (e.getCause() != null) {
                reportError(e.getCause().getMessage(), e.getCause());
            } else {
                reportError(e.getMessage(), e);
            }
        } catch (IOException e) {
            Debug.out("recoder2key: IOException detected in: " + block, e);
            block = trim(block, 25);
            reportError("Could not access data stream " + "(e.g. file not found, wrong permissions) " + "when reading " + block + ": " + trim(e.getMessage()),
                    e);
        } catch (NullPointerException e) {
            // to retrieve a more precise message we would need to patch Recoder
            reportError("Recoder parser threw exception in block:\n" + block + "\n Probably a misspelled identifier name.", e);
        } catch (Exception e) {
            reportError(e.getMessage(), e);
        } finally {
            if (sr != null) {
        	try {
	            sr.close();
                } catch (IOException e) {
                }
            }
        }
        return bl;
    }

    /**
     * parses a given JavaBlock using the context to determine the right
     * references
     * 
     * @param block
     *            a String describing a java block
     * @param context
     *            recoder.java.CompilationUnit in which the block has to be
     *            interprested
     * @return the parsed and resolved JavaBlock
     */
    public JavaBlock readBlock(String block, Context context) {

        recoder.java.StatementBlock sb = recoderBlock(block, context);
        JavaBlock jb = JavaBlock.createJavaBlock((StatementBlock) getConverter().process(sb));
        return jb;
    }

    /**
     * parses a given JavaBlock using the context to determine the right
     * references using an empty context
     * 
     * @param block
     *            a String describing a java block
     * @return the parsed and resolved JavaBlock
     */
    public JavaBlock readBlockWithEmptyContext(String block) {
        return readBlock(block, createEmptyContext());
    }

    /**
     * parses a given JavaBlock using a namespace to determine the right
     * references using an empty context. The variables of the namespace are
     * used to create a new class context
     * 
     * @param s
     *            a String describing a java block
     * @return the parsed and resolved JavaBlock
     */
    public JavaBlock readBlockWithProgramVariables(Namespace varns, String s) {
        Iterator<Named> it = varns.allElements().iterator();
        ImmutableList<ProgramVariable> pvs = ImmutableSLList.<ProgramVariable>nil();
        while (it.hasNext()) {
            Named n = it.next();
            if (n instanceof ProgramVariable) {
                pvs = pvs.append((ProgramVariable) n); //preserve the order (nested namespaces!) 
            }
        }
        return readBlock(s, createContext(pvs));
    }

    /**
     * make a new classdeclaration with a temporary name.
     * 
     * The name is a unique implicit identifier.
     * 
     * @return a newly created recoder ClassDeclaration with a unique name
     */
    private recoder.java.declaration.ClassDeclaration interactClassDecl() {
        recoder.java.declaration.ClassDeclaration classContext = new recoder.java.declaration.ClassDeclaration(null, new ImplicitIdentifier(
                "<virtual_class_for_parsing" + interactCounter + ">"), null, null, null);
        interactCounter++;
        classContext.setProgramModelInfo(servConf.getCrossReferenceSourceInfo());
        return classContext;
    }

    // ----- helpers

    /**
     * reduce the size of a string to a maximum of 150 characters. Introduces
     * ellipses [...]
     */
    private static String trim(String s) {
        return trim(s, 150);
    }

    /**
     * reduce the size of a string to a maximum of length.
     */
    private static String trim(String s, int length) {
        if (s.length() > length)
            return s.substring(0, length - 5) + "[...]";
        return s;
    }

    // ----- error handling

    /**
     * tries to parse recoders exception position information
     */
    private static int[] extractPositionInfo(String errorMessage) {
        if (errorMessage == null || errorMessage.indexOf('@') == -1) {
            return new int[0];
        }
        int line = -1;
        int column = -1;
        try {
            String pos = errorMessage.substring(errorMessage.indexOf("@") + 1);
            pos = pos.substring(0, pos.indexOf(" "));
            line = Integer.parseInt(pos.substring(0, pos.indexOf('/')));
            column = Integer.parseInt(pos.substring(pos.indexOf('/') + 1));
        } catch (NumberFormatException nfe) {
            Debug.out("recoder2key:unresolved reference at " + "line:" + line + " column:" + column);
            return new int[0];
        } catch (StringIndexOutOfBoundsException siexc) {
            return new int[0];
        }
        return new int[] { line, column };
    }

    /**
     * report an error in form of a ConvertException. The cause is always
     * attached to the resulting exception.
     * 
     * @param message
     *            message to be used.
     * @param t
     *            the cause of the exceptional case
     * @throws ConvertException
     *             always
     */
    public static void reportError(String message, Throwable t) {
        // Attention: this highly depends on Recoders exception messages!
	Throwable cause = t;
	if  (t instanceof ExceptionHandlerException) {
	    if (t.getCause() != null) {
		cause = t.getCause();
	    } 
	}
	int[] pos = extractPositionInfo(cause.toString());
        final RuntimeException rte;
        if (pos.length > 0) {
            rte = new PosConvertException(message, pos[0], pos[1]);
            rte.initCause(cause);
        } else {
            rte = new ConvertException(message);
            rte.initCause(cause);
        }

        throw rte;
    }

}
