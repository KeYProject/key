// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;
import java.io.StringReader;
import java.net.URL;
import java.util.HashMap;
import java.util.Iterator;

import recoder.list.CompilationUnitArrayList;
import recoder.list.CompilationUnitList;
import recoder.list.CompilationUnitMutableList;
import recoder.list.MemberDeclarationArrayList;
import recoder.list.MemberDeclarationMutableList;
import recoder.service.ChangeHistory;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.FieldSpecification;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.recoderext.ClassInitializeMethodBuilder;
import de.uka.ilkd.key.java.recoderext.ClassPreparationMethodBuilder;
import de.uka.ilkd.key.java.recoderext.ConstructorNormalformBuilder;
import de.uka.ilkd.key.java.recoderext.CreateBuilder;
import de.uka.ilkd.key.java.recoderext.CreateObjectBuilder;
import de.uka.ilkd.key.java.recoderext.ExtendedIdentifier;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.java.recoderext.ImplicitIdentifier;
import de.uka.ilkd.key.java.recoderext.InstanceAllocationMethodBuilder;
import de.uka.ilkd.key.java.recoderext.JVMIsTransientMethodBuilder;
import de.uka.ilkd.key.java.recoderext.KeYCrossReferenceServiceConfiguration;
import de.uka.ilkd.key.java.recoderext.KeYCrossReferenceSourceInfo;
import de.uka.ilkd.key.java.recoderext.PrepareObjectBuilder;
import de.uka.ilkd.key.java.recoderext.RecoderModelTransformer;
import de.uka.ilkd.key.java.recoderext.URLDataLocation;
import de.uka.ilkd.key.logic.IteratorOfNamed;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.IteratorOfProgramVariable;
import de.uka.ilkd.key.logic.op.ListOfProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SLListOfProgramVariable;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.KeYResourceManager;

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
     * The location where the libraries to be parsed can be found. It will be
     * used as a resource path relative to the path of the package.
     */
    private static String JAVA_SRC_DIR = "JavaRedux_1.4.2";

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
    public Recoder2KeY(KeYCrossReferenceServiceConfiguration servConf, KeYRecoderMapping rec2key, NamespaceSet nss, TypeConverter tc) {
        this(servConf, null, rec2key, nss, tc);
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
     *            nthe namespaces to work upon, not null
     */
    public Recoder2KeY(Services services, NamespaceSet nss) {
        this(services.getJavaInfo().getKeYProgModelInfo().getServConf(), null, services.getJavaInfo().rec2key(), nss, services.getTypeConverter());
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
    public Recoder2KeY(KeYCrossReferenceServiceConfiguration servConf, String classPath, KeYRecoderMapping rec2key, NamespaceSet nss, TypeConverter tc) {

        if (servConf == null)
            throw new IllegalArgumentException("service configuration is null");

        if (rec2key == null)
            throw new IllegalArgumentException("rec2key mapping is null");

        if (nss == null)
            throw new IllegalArgumentException("namespaces is null");

        this.servConf = servConf;
        this.mapping = rec2key;
        this.converter = makeConverter();
        this.typeConverter = new Recoder2KeYTypeConverter(tc, nss, this);

        // set up recoder:
        recoder.util.Debug.setLevel(500);

       if (classPath != null) {
            servConf.getProjectSettings().setProperty(recoder.io.PropertyNames.INPUT_PATH, classPath);
        }

        // make sure java.lang.Object as class file within reach.
        // TODO is this really still desired?
        // ClassFileRepository cfr = servConf.getClassFileRepository();
        // if (cfr.findClassFile("java.lang.Object") == null) {
        // Debug.out("System classes not found in path.");
        // }
        
        if (servConf.getProjectSettings().
	    ensureSystemClassesAreInPath()) {
	} else {
	    if (System.getProperty("os.name").toLowerCase().indexOf("mac") != -1) {
		String inputPath = servConf.getProjectSettings().
		    getProperty(recoder.io.PropertyNames.INPUT_PATH);
		if (inputPath == null) {
                    inputPath = ".";
		}
		 
		final String javaHome = System.getProperty("java.home");
		 
		inputPath +=  File.pathSeparator + javaHome + File.separator +
		    ".." + File.separator + "Classes"+ File.separator + "classes.jar";
		inputPath +=  File.pathSeparator + javaHome + File.separator +
		    ".."+ File.separator + "Classes"+ File.separator + "ui.jar";
						   
		servConf.getProjectSettings().
		    setProperty(recoder.io.PropertyNames.INPUT_PATH, inputPath);
						   
		if (!servConf.getProjectSettings().
		    ensureSystemClassesAreInPath()) {
		    System.err.println("System classes not found on default Mac places.");
		}
	    
	    } else {
		System.err.println("System classes not found in path.");
	    }
	}
    }
    
    /**
     * create the ast converter. This is overwritten in SchemaRecoder2KeY to use
     * schema-aware converters.
     * 
     * @return a newley created converter
     */
    protected Recoder2KeYConverter makeConverter() {
        return new Recoder2KeYConverter(this);
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

    public CompilationUnit[] readCompilationUnitsAsFiles(String[] cUnitStrings) {
        recoder.list.CompilationUnitList cUnits = recoderCompilationUnitsAsFiles(cUnitStrings);
        CompilationUnit[] result = new CompilationUnit[cUnits.size()];
        for (int i = 0, sz = cUnits.size(); i < sz; i++) {
            Debug.out("converting now " + cUnitStrings[i]);
            result[i] = getConverter().processCompilationUnit(cUnits.getCompilationUnit(i), cUnitStrings[i]);
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
    private recoder.list.CompilationUnitList recoderCompilationUnitsAsFiles(String[] cUnitStrings) {
        recoder.list.CompilationUnitMutableList cUnits = new recoder.list.CompilationUnitArrayList();
        parseSpecialClasses();
        try {
            cUnits = servConf.getProgramFactory().parseCompilationUnits(cUnitStrings);
            final ChangeHistory changeHistory = servConf.getChangeHistory();
            for (int i = 0, sz = cUnits.size(); i < sz; i++) {
                cUnits.getCompilationUnit(i).makeAllParentRolesValid();
                changeHistory.attached(cUnits.getCompilationUnit(i));
            }

            if (changeHistory.needsUpdate()) {
                changeHistory.updateModel();
            }

            // transform program
            transformModel(cUnits);
        } catch (recoder.service.AmbiguousDeclarationException ade) {
            reportError(ade.getMessage(), ade);
        } catch (recoder.ParserException pe) {
            reportError(pe.getMessage(), pe);
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
    public CompilationUnit readCompilationUnit(String cUnitString) {
        final recoder.java.CompilationUnit cc = recoderCompilationUnits(new String[] { cUnitString }).getCompilationUnit(0);
        return (CompilationUnit) getConverter().process(cc);
    }

    /**
     * read a number of compilation units, each given as a string.
     * 
     * @param cUnitStrings
     *            an array of strings, each element represents a compilation
     *            unit
     * @return a list of KeY structured compilation units.
     */
    private CompilationUnitList recoderCompilationUnits(String[] cUnitStrings) {

        parseSpecialClasses();
        CompilationUnitMutableList cUnits = new CompilationUnitArrayList();
        int current = 0;
        try {
            for (int i = 0; i < cUnitStrings.length; i++) {
                current = i;
                Debug.out("Reading " + trim(cUnitStrings[i]));
                cUnits.add(servConf.getProgramFactory().parseCompilationUnit(new StringReader(cUnitStrings[i])));
            }
            // run cross referencer
            final ChangeHistory changeHistory = servConf.getChangeHistory();
            for (int i = 0, sz = cUnits.size(); i < sz; i++) {
                current = i;
                cUnits.getCompilationUnit(i).makeAllParentRolesValid();
                changeHistory.attached(cUnits.getCompilationUnit(i));
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
        }
        return cUnits;
    }

    // ----- parsing libraries

    /**
     * adds a special compilation unit containing references to types that have
     * to be available in Recoder and KeY form, e.g. Exceptions
     * 
     * @todo
     */
    private recoder.list.CompilationUnitMutableList parseSpecial(boolean parseLibs) {
        recoder.ProgramFactory pf = servConf.getProgramFactory();
        recoder.list.CompilationUnitMutableList rcuList = new recoder.list.CompilationUnitArrayList();
        recoder.java.CompilationUnit rcu = null;
        URL jlURL = KeYResourceManager.getManager().getResourceFile(Recoder2KeY.class, JAVA_SRC_DIR + "/" + "JAVALANG.TXT");
        if (jlURL == null) {
            Debug.out(JAVA_SRC_DIR + "/" + "JAVALANG.TXT not found!");
        }
        if (jlURL != null && Debug.ENABLE_DEBUG) {
            Debug.out(jlURL.toString());
        }
        try {
            BufferedReader r = new BufferedReader(new InputStreamReader(jlURL.openStream()));
            for (String jl = r.readLine(); (jl != null); jl = r.readLine()) {
                if ((jl.charAt(0) == '#') || (jl.length() == 0)) {
                    continue;
                }
                if ((jl.charAt(0) == '+')) {
                    if (parseLibs) {
                        jl = jl.substring(1);
                    } else {
                        continue;
                    }
                }
                jl = jl.trim();
                URL jlf = KeYResourceManager.getManager().getResourceFile(Recoder2KeY.class, JAVA_SRC_DIR + "/" + jl);
                InputStream is = jlf.openStream();
                if (is == null)
                    throw new IOException("Resource cannot be opened for reading: " + jlf);
                Reader f = new BufferedReader(new InputStreamReader(is));
                rcu = pf.parseCompilationUnit(f);
                rcu.setDataLocation(new URLDataLocation(jlf));
                rcu.makeAllParentRolesValid();
                rcuList.add(rcu);
                if (Debug.ENABLE_DEBUG) {
                    Debug.out("parsed: " + jl);
                }
            }

            // parse a special default class
            rcu = pf.parseCompilationUnit(new StringReader("public class " + JavaInfo.DEFAULT_EXECUTION_CONTEXT_CLASS + " {}"));
            rcu.makeAllParentRolesValid();
            rcuList.add(rcu);
        } catch (recoder.ParserException e) {
            Debug.out("Error while parsing specials", e);
            System.err.println("recoder2key: Error while parsing specials");
            System.err.println("recoder2key: Try to continue...");
        } catch (Exception e) {
            Debug.out("Error while parsing specials, someone messed up with the resources", e);
            System.err.println("recoder2key: Error while parsing specials");
            System.err.println("recoder2key: someone messed up with the resources");
        }
        return rcuList;
    }

    /**
     * makes sure that the special classes (library classes) have been parsed
     * in.
     * 
     * If not parsed yet, the special classes are read in and converted.
     */
    public void parseSpecialClasses() {
        if (mapping.parsedSpecial()) {
            return;
        }

        // go to special mode -> used by the converter!
        setParsingLibs(true);

        recoder.list.CompilationUnitMutableList specialClasses = parseSpecial(KeYUserProblemFile.parseLibSpecs);

        ChangeHistory changeHistory = servConf.getChangeHistory();
        for (int i = 0, sz = specialClasses.size(); i < sz; i++) {
            specialClasses.getCompilationUnit(i).makeAllParentRolesValid();
            changeHistory.attached(specialClasses.getCompilationUnit(i));
        }

        if (changeHistory.needsUpdate()) {
            changeHistory.updateModel();
        }

        transformModel(specialClasses);

        // make them available to the rec2key mapping
        for (int i = 0, sz = specialClasses.size(); i < sz; i++) {
            getConverter().process(specialClasses.getCompilationUnit(i));
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

    private void transformModel(CompilationUnitMutableList cUnits) {

        RecoderModelTransformer[] transformer = new RecoderModelTransformer[] {
                // reinsert when java 5 is enabled
                // new EnumClassBuilder(servConf, cUnits),
                new ImplicitFieldAdder(servConf, cUnits), new InstanceAllocationMethodBuilder(servConf, cUnits),
                new ConstructorNormalformBuilder(servConf, cUnits), new ClassPreparationMethodBuilder(servConf, cUnits),
                new ClassInitializeMethodBuilder(servConf, cUnits), new PrepareObjectBuilder(servConf, cUnits), new CreateBuilder(servConf, cUnits),
                new CreateObjectBuilder(servConf, cUnits), new JVMIsTransientMethodBuilder(servConf, cUnits) };

        final ChangeHistory cHistory = servConf.getChangeHistory();
        for (int i = 0; i < transformer.length; i++) {
            if (Debug.ENABLE_DEBUG) {
                Debug.out("current transformer : " + transformer[i].toString());
            }
            transformer[i].execute();
        }
        if (cHistory.needsUpdate()) {
            cHistory.updateModel();
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

        // add method to memberdeclaration list
        MemberDeclarationMutableList memberList = classContext.getMembers();

        if (memberList == null) {
            memberList = new MemberDeclarationArrayList(1);
            classContext.setMembers(memberList);
        }

        for (int i = 0, sz = memberList.size(); i < sz; i++) {
            if (memberList.getMemberDeclaration(i) instanceof recoder.java.declaration.MethodDeclaration) {
                recoder.java.declaration.MethodDeclaration olddecl = (recoder.java.declaration.MethodDeclaration) memberList.getMemberDeclaration(i);
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
     * create a new context with a temproray name and make a list of variables
     * visible from within. Use the default source info.
     * 
     * @param pvs
     *            a list of variables
     * @return a newly created context.
     */

    protected Context createContext(ListOfProgramVariable pvs) {
        return createContext(pvs, servConf.getCrossReferenceSourceInfo());
    }

    /**
     * create a new Context with a temproray name and make a list of variables
     * visible from within.
     * 
     * @param vars
     *            a list of variables
     * @param csi
     *            a special source info
     * 
     * @return a newly created context.
     */
    protected Context createContext(ListOfProgramVariable vars, recoder.service.CrossReferenceSourceInfo csi) {
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
    private void addProgramVariablesToClassContext(recoder.java.declaration.ClassDeclaration classContext, ListOfProgramVariable vars,
            recoder.service.CrossReferenceSourceInfo csi) {

        HashMap names2var = new HashMap();
        IteratorOfProgramVariable it = vars.iterator();
        java.util.HashSet names = new java.util.HashSet();
        recoder.list.MemberDeclarationMutableList list = classContext.getMembers();

        // perhaps install a new list for the members of the class context
        if (list == null) {
            list = new recoder.list.MemberDeclarationArrayList();
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
            typeName = javaType.getFullName();

            recoder.java.declaration.FieldDeclaration recVar = new recoder.java.declaration.FieldDeclaration(null, name2typeReference(typeName),
                    new ExtendedIdentifier(keyVarSpec.getName()), null);

            list.add(recVar);
            classContext.makeAllParentRolesValid();
            recoder.java.declaration.VariableSpecification rvarspec = recVar.getVariables().getVariableSpecification(0);
            names2var.put(var.name().toString(), rvarspec);

            rvarspec.setProgramModelInfo(csi);
            insertToMap(recVar.getVariables().getVariableSpecification(0), keyVarSpec);
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
        Iterator it = mapping.elemsKeY().iterator();
        while (it.hasNext()) {
            Object o = it.next();
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
        while (idx != -1) {
            pr = new recoder.java.reference.PackageReference(pr, new recoder.java.Identifier(baseType.substring(lastIndex, idx)));
            lastIndex = idx + 1;
            idx = baseType.indexOf('.', lastIndex);
        }

        recoder.java.Identifier typeId;
        if (baseType.charAt(0) == '<') {
            typeId = new ImplicitIdentifier(baseType.substring(lastIndex));
        } else {
            typeId = new recoder.java.Identifier(baseType.substring(lastIndex));
        }
        recoder.java.reference.TypeReference result = new recoder.java.reference.TypeReference(pr, typeId);
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
        try {
            bl = servConf.getProgramFactory().parseStatementBlock(new StringReader(block));
            bl.makeAllParentRolesValid();
            embedMethod(embedBlock(bl), context);
            context.getCompilationUnitContext().makeParentRoleValid();
            // servConf.getCrossReferenceSourceInfo().register(bl);
            // register() is deprecated. so use this instead:
            servConf.getChangeHistory().attached(bl);
            servConf.getChangeHistory().attached(context.getCompilationUnitContext());
            servConf.getChangeHistory().updateModel();
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
        IteratorOfNamed it = varns.allElements().iterator();
        ListOfProgramVariable pvs = SLListOfProgramVariable.EMPTY_LIST;
        while (it.hasNext()) {
            Named n = it.next();
            if (n instanceof ProgramVariable) {
                pvs = pvs.prepend((ProgramVariable) n);
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
        String pos = errorMessage.substring(errorMessage.indexOf("@") + 1);
        pos = pos.substring(0, pos.indexOf(" "));
        int line = -1;
        int column = -1;
        try {
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
     * @param e
     *            the cause of the exceptional case
     * @throws ConvertException
     *             always
     */
    public static void reportError(String message, Throwable e) {
        // Attention: this highly depends on Recoders exception messages!
        int[] pos = extractPositionInfo(e.toString());
        final RuntimeException rte;
        if (pos.length > 0) {
            rte = (PosConvertException) new PosConvertException(message, pos[0], pos[1]).initCause(e);
        } else {
            rte = new ConvertException(message, e);
        }

        throw rte;
    }

}
