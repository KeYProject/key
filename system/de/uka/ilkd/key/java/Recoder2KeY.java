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
import java.io.*;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.net.URL;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;

import org.apache.log4j.Logger;

import recoder.abstraction.ClassType;
import recoder.bytecode.ClassFile;
import recoder.list.ClassTypeList;
import recoder.list.ExpressionMutableList;
import recoder.list.LoopInitializerMutableList;
import recoder.service.ChangeHistory;
import de.uka.ilkd.key.java.abstraction.*;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.declaration.modifier.*;
import de.uka.ilkd.key.java.declaration.modifier.Ghost;
import de.uka.ilkd.key.java.declaration.modifier.Model;
import de.uka.ilkd.key.java.expression.ArrayInitializer;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.expression.PassiveExpression;
import de.uka.ilkd.key.java.expression.literal.*;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.expression.operator.SetAssignment;
import de.uka.ilkd.key.java.recoderext.*;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.*;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;
import de.uka.ilkd.key.util.KeYResourceManager;

public class Recoder2KeY implements JavaReader{
    
    static Logger logger = Logger.getLogger(Recoder2KeY.class.getName());
    //static String javaSrcDir = "sun_src_1.3.1_11-b02";
    //static String javaSrcDir = "sun_src_1.4.2_03";
    static String javaSrcDir = "JavaRedux_1.4.2";

    /** caches access to methods for reflection */
    private final static HashMap ct2meth = new HashMap(400);

    /** caches constructor access for reflection */
    private final static HashMap recClass2keyClassCons = new HashMap(400);

    /**
     *   mapping from recoder.abstraction.Type to KeYJavaType
     */
    protected HashMap type2KeYType = new HashMap();

    /**
     *  methodsDeclaring contains the recoder method declarations as keys 
     *  that have been started to convert but are not yet finished.
     *  The mapped value is the reference to the later completed 
     *  ProgramMethod.
     */
    protected HashMap methodsDeclaring = new HashMap();

    /**
     * Hashmap from
     * <code>recoder.java.declaration.FieldSpecification</code> to
     * <code>ProgramVariable</code>; this is necessary to avoid cycles
     * when converting initializers. Access to this map is performed
     * via the method
     * <code>getProgramVariableForFieldSpecification</code>
     */
    protected HashMap fieldSpecificationMapping = new HashMap ();

    protected KeYRecoderMapping rec2key;
    protected TypeConverter typeConverter;
    protected KeYCrossReferenceServiceConfiguration servConf;
    protected Services services;

    private NamespaceSet namespaces = new NamespaceSet ();

    private static int interactCounter = 0;
    private String currentClass = null;
    private boolean parsingLibs = false;

    private  boolean inLoopInit = false;
    String fileName;

    /**
     * builder class for implicit array methods
     */
    private CreateArrayMethodBuilder arrayMethodBuilder;

    /**
     * builder class for implicit transient array methods
     */
    private CreateTransientArrayMethodBuilder transientArrayMethodBuilder;

    public Recoder2KeY(KeYCrossReferenceServiceConfiguration servConf,
		       KeYRecoderMapping rec2key,
		       NamespaceSet nss,
		       TypeConverter tc) {
	this(servConf, null, rec2key, nss, tc);
    }


    public Recoder2KeY(Services services, NamespaceSet nss) {
	this(services.getJavaInfo().getKeYProgModelInfo().getServConf(), 
	     null, 
	     services.getJavaInfo().rec2key(),
	     nss,
	     services.getTypeConverter());
    }


    private Recoder2KeY(KeYCrossReferenceServiceConfiguration servConf,
			String classPath,
			KeYRecoderMapping rec2key,
			NamespaceSet nss,
			TypeConverter tc) {
	this.servConf      = servConf;
	this.typeConverter = tc;
	this.rec2key       = rec2key;	
	this.services	   = tc.getServices();
        if(classPath != null) {
	    servConf.getProjectSettings().setProperty
		(recoder.io.PropertyNames.INPUT_PATH, classPath);
	}

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
	namespaces = nss;	
    }


    private void initArrayMethodBuilder() {
	final KeYJavaType integerType = getKeYJavaType(servConf.getNameInfo().getIntType());
	final KeYJavaType byteType    = getKeYJavaType(servConf.getNameInfo().getByteType());
	final KeYJavaType objectType  = javaInfo().getJavaLangObject();
	arrayMethodBuilder          = new CreateArrayMethodBuilder(integerType, 
								   objectType);
	transientArrayMethodBuilder = new CreateTransientArrayMethodBuilder(integerType, 
									    objectType, 
									    byteType);
    }

    private void parsingLibs(boolean v) {
	parsingLibs = v;
    }

    private JavaInfo javaInfo() {
	return typeConverter != null ?
	    typeConverter.getServices().getJavaInfo() :
	    null;
    }

    public KeYCrossReferenceServiceConfiguration getServiceConfiguration() {
	return servConf;
    }


    public KeYRecoderMapping rec2key() {
	return rec2key;
    }


    /**
     * wraps a RECODER StatementBlock in a method
     * @param block the recoder.java.StatementBlock to wrap
     * @return the enclosing recoder.java.MethodDeclaration
     */
    protected recoder.java.declaration.MethodDeclaration
	embedBlock(recoder.java.StatementBlock block) {

	/*
	   MethodDeclaration(modifiers,return type,Identifier, parameters,
	                     throws, StatementBlock)
	 */
	recoder.java.declaration.MethodDeclaration mdecl=new 
	    recoder.java.declaration.MethodDeclaration
	    (null, null, new ImplicitIdentifier("<virtual_method_for_parsing>"), 
	     null, null, block);
	mdecl.makeParentRoleValid();
	return mdecl;
    }  


    /**
     * wraps a RECODER MethodDeclaration in a class
     * @param mdecl the recoder.java.declaration.MethodDeclaration to wrap
     * @param context the recoder.java.declaration.ClassDeclaration
     * where the method has to be embedded
     * @return the enclosing recoder.java.declaration.ClassDeclaration
     */
    protected recoder.java.declaration.ClassDeclaration
	embedMethod(recoder.java.declaration.MethodDeclaration mdecl,
		    Context context) {

	recoder.java.declaration.ClassDeclaration 
	    classContext = context.getClassContext();
        
        
	// add method to memberdeclaration list
	recoder.list.MemberDeclarationMutableList memberList = 
	    classContext.getMembers();

	if (memberList == null) {
	    memberList = new recoder.list.MemberDeclarationArrayList(1); 
	    classContext.setMembers(memberList);
	} 

	for (int i=0, sz=memberList.size(); i<sz; i++) {
	    if (memberList.getMemberDeclaration(i) 
		instanceof recoder.java.declaration.MethodDeclaration) {
		recoder.java.declaration.MethodDeclaration olddecl
		    = (recoder.java.declaration.MethodDeclaration) 
		    memberList.getMemberDeclaration(i);
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


    protected recoder.list.CompilationUnitMutableList recoderCompilationUnits
	(String[] cUnitStrings) {
	recoder.util.Debug.setLevel(500);
	parseSpecialClasses();
	recoder.list.CompilationUnitMutableList cUnits
	    = new recoder.list.CompilationUnitArrayList();	
	int current = 0;
	try {
	    for (int i=0; i<cUnitStrings.length; i++) {
                current = i;
		Debug.out("Reading ", cUnitStrings[i]);
		cUnits.add(servConf.getProgramFactory().parseCompilationUnit
			   (new StringReader(cUnitStrings[i]))); 
	    }
	    // run cross referencer
            final ChangeHistory changeHistory = servConf.getChangeHistory();
	    for (int i=0, sz = cUnits.size(); i<sz; i++) {
		current = i;
                cUnits.getCompilationUnit(i).makeAllParentRolesValid();
		changeHistory.attached(cUnits.getCompilationUnit(i));
	    }
            
            if (changeHistory.needsUpdate()) {
		changeHistory.updateModel();
	    }             
 	    // transform program

	    transformModel(cUnits);
	} catch(IOException ioe) {
	    Debug.out("recoder2key: IO Error when reading"+
		      "compilation unit (unit, exception) ", 
		      cUnitStrings[current], ioe);		
	    reportError("IOError reading java program " + cUnitStrings[current] +
			". May be file not found or missing permissions.", ioe);
	} catch(recoder.ParserException pe) {
	    Debug.out("recoder2key: Recoder Parser Error when" +
		      "reading a comiplation unit (unit, exception)",
		      cUnitStrings[current], pe);		
	    if (pe.getCause()!=null) {
		reportError(pe.getCause().getMessage(), pe.getCause());
	    } else {
		reportError(pe.getMessage(), pe);
	    }	    
	}			
	return cUnits;
    }

    protected recoder.list.CompilationUnitMutableList recoderCompilationUnitsAsFiles(String[] cUnitStrings) {
	recoder.list.CompilationUnitMutableList cUnits
	    = new recoder.list.CompilationUnitArrayList();
	parseSpecialClasses();
	try {
	    cUnits = servConf.getProgramFactory().parseCompilationUnits(cUnitStrings);
	    final ChangeHistory changeHistory = servConf.getChangeHistory();
            for (int i = 0, sz = cUnits.size(); i<sz; i++) {
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
	} catch(recoder.ParserException pe) {
	    reportError(pe.getMessage(), pe);
	}
	return cUnits;
    }

    /**
     * adds a special compilation unit containing references to types that
     * have to be available in Recoder and KeY form, e.g. Exceptions
     * TODO
     */
    private recoder.list.CompilationUnitMutableList parseSpecial(boolean parseLibs) {
    	recoder.ProgramFactory pf = servConf.getProgramFactory();
    	recoder.list.CompilationUnitMutableList rcuList = new recoder.list.CompilationUnitArrayList();
    	recoder.java.CompilationUnit rcu = null;
    	URL jlURL = KeYResourceManager.getManager().getResourceFile(
    			Recoder2KeY.class, javaSrcDir + "/" + "JAVALANG.TXT");    		
    	if (logger.isDebugEnabled()) {
    		logger.debug(jlURL.toString());
    	}
    	try {
	    BufferedReader r = new BufferedReader(new InputStreamReader(jlURL.openStream()));
    		for (String jl = r.readLine();(jl != null); jl = r.readLine()) {
    			if ((jl.charAt(0) == '#') || (jl.length() == 0)) {
    				continue;
    			}
			if ((jl.charAt(0) == '+')){
			    if (parseLibs){
				jl = jl.substring(1);
			    } else{
				continue;
			    }
			}
			jl = jl.trim();
    			URL jlf = KeYResourceManager.getManager().getResourceFile(
    	    			Recoder2KeY.class, javaSrcDir + "/" + jl);
    			Reader f = new BufferedReader
			    (new InputStreamReader(jlf.openStream()));
    			rcu = pf.parseCompilationUnit(f);
    			rcu.makeAllParentRolesValid();
    			rcuList.add(rcu);
    			if (logger.isDebugEnabled()) {
    				logger.debug("parsed: " + jl);
    			}
    		}

    		// parse a special default class    		    		
    		rcu = pf.parseCompilationUnit
		        (new StringReader
	    		        ("public class "+
	    		                JavaInfo.DEFAULT_EXECUTION_CONTEXT_CLASS +" {}"));
    		rcu.makeAllParentRolesValid();
    		rcuList.add(rcu);    		    		
    	} catch (recoder.ParserException e) {
    		e.printStackTrace(System.out);
    		System.err.println("recoder2key: Error while parsing specials");
    		System.err.println("recoder2key: Try to continue...");
    	} catch (IOException e) {
    		e.printStackTrace(System.out);
    		System.err.println("recoder2key: Error while parsing specials");
    		System.err.println("recoder2key: someone messed up with the resources");
    	}
    	return rcuList;
    }

    /** 
     * if not parsed yet the special classes are read in and converted 
     */
    public void parseSpecialClasses() {
	if (rec2key.parsedSpecial()) {
	    return;
	}
	parsingLibs(true);

	final recoder.list.
	    CompilationUnitMutableList specialClasses = parseSpecial(false);
	final ChangeHistory changeHistory = servConf.getChangeHistory();
	for (int i = 0, sz = specialClasses.size(); i<sz; i++) {
	    specialClasses.getCompilationUnit(i).makeAllParentRolesValid();
	    changeHistory.attached(specialClasses.getCompilationUnit(i));
	}
	
	if (changeHistory.needsUpdate()) {
	    changeHistory.updateModel();
	} 

	transformModel(specialClasses);

	for (int i=0, sz = specialClasses.size(); i<sz; i++) {
	    currentClass = specialClasses.getCompilationUnit(i).getName(); //TODO: use the real file name here
	    callConvert(specialClasses.getCompilationUnit(i));
	    currentClass = null;
	}

	rec2key().parsedSpecial(true);
	parsingLibs(false);
    }

    public CompilationUnit[] readCompilationUnitsAsFiles(String[] cUnitStrings) {
	recoder.list.CompilationUnitMutableList cUnits =
	    recoderCompilationUnitsAsFiles(cUnitStrings);
	CompilationUnit[] result = new CompilationUnit[cUnits.size()];
	for (int i=0, sz = cUnits.size(); i<sz; i++) {
	    Debug.out("R2K: ", cUnitStrings[i]);
            currentClass = cUnitStrings[i];
	    result[i] = convert(cUnits.getCompilationUnit(i));
            currentClass = null;
	}
	return result;
    }

    public CompilationUnit readCompilationUnit(String cUnitString) { 
	final recoder.java.CompilationUnit cc = recoderCompilationUnits
	    (new String[]{cUnitString}).getCompilationUnit(0);
	return (CompilationUnit) callConvert(cc);
    }


    private String trim(String s) {
	if (s.length()>150) return s.substring(0,150)+"[...]";
	return s;
    }

    /**
     * tries to parse recoders exception position information
     */
    protected int[] extractPositionInfo(String errorMessage) {
        if (errorMessage == null || errorMessage.indexOf('@') == -1) { 
	    return new int[0];
	}
	String pos = errorMessage.substring(errorMessage.indexOf("@")+1);
	pos = pos.substring(0, pos.indexOf(" ")); 
	int line   = -1;
	int column = -1;
	try {
	    line   = Integer.parseInt(pos.substring(0,pos.indexOf('/')));
	    column = Integer.parseInt(pos.substring(pos.indexOf('/')+1));
	} catch (NumberFormatException nfe) {
	    Debug.out("recoder2key:unresolved reference at "+
		      "line:"+line+" column:"+column);
	    return new int[0];
	} catch (StringIndexOutOfBoundsException siexc){
	    return new int[0];
	}
	return new int[]{line, column};
    }

    
    protected void reportError(String message, Throwable e) {
	// Attention: this highly depends on Recoders exception messages!
	int[] pos = extractPositionInfo(e.toString());
	final RuntimeException rte;
	if (pos.length > 0) {
	    rte = new PosConvertException(message, pos[0], pos[1]);
	} else {
	    if(e instanceof recoder.parser.ParseException){
		rte = new ConvertException((recoder.parser.ParseException) e);
	    }else if(e instanceof de.uka.ilkd.key.parser.proofjava.ParseException){
		rte = new ConvertException((de.uka.ilkd.key.parser.
					    proofjava.ParseException) e);
	    }else{
		rte = new ConvertException(message);
	    }
	}	
	throw (RuntimeException) rte.initCause(e);
    }

    /** 
     * parses a given JavaBlock using the context to determine the right 
     * references and returns a statement block of recoder.
     * @param block a String describing a java block
     * @param context recoder.java.CompilationUnit in which the block has 
     * to be interpreted
     * @return the parsed and resolved recoder statement block
     */
    protected recoder.java.StatementBlock recoderBlock(String block,
						       Context context) {
	recoder.java.StatementBlock bl = null;       
	parseSpecialClasses();
	try {
	    bl = servConf.getProgramFactory().
		parseStatementBlock(new StringReader(block)); 
	    bl.makeAllParentRolesValid();
	    embedMethod(embedBlock(bl), context);
	    context.getCompilationUnitContext().makeParentRoleValid();
 	    servConf.getCrossReferenceSourceInfo().register(bl);
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
	    Debug.out("recoder2key: IOException detected. "+
		      "(parsed program, IOException)", block, e);
	    if (block.length()>20) block = block.substring(0,20)+"...";
	    reportError("Could not access data stream " +
			"(e.g. file not found, wrong permissions) "+
			"when reading "+ block + ": "+trim(e.getMessage()), e);
	} catch (NullPointerException e){
	    //to retrieve a more precise message we would need to patch Recoder
	    reportError
		("Recoder parser threw exception in block:\n" + block +
		 "\n Probably a misspelled identifier name.", e);
	} catch (Exception e) {
	    reportError(e.getMessage(), e);
	}
	return bl;
    } 

    /** parses a given JavaBlock using the context to determine the right 
     * references
     * @param block a String describing a java block
     * @param context recoder.java.CompilationUnit in which the block has 
     * to be interprested
     * @return the parsed and resolved JavaBlock
     */
    public JavaBlock readBlock(String block,
			       Context context) { 

        recoder.java.StatementBlock sb = recoderBlock(block, context);
	JavaBlock jb = JavaBlock.createJavaBlock
	    ((StatementBlock)callConvert(sb));
	return jb;
    }


    /** parses a given JavaBlock using the context to determine the right 
     * references using an empty context
     * @param block a String describing a java block
     * @return the parsed and resolved JavaBlock
     */
    public JavaBlock readBlockWithEmptyContext(String block) { 
	return readBlock(block, createEmptyContext());
    }

    public JavaBlock readBlockWithProgramVariables(Namespace varns, String s) {
	IteratorOfNamed it = varns.allElements().iterator();
	ListOfProgramVariable pvs = SLListOfProgramVariable.EMPTY_LIST;
	while (it.hasNext()) {
	    Named n = it.next();
	    if (n instanceof ProgramVariable) {
		pvs=pvs.prepend((ProgramVariable)n);
	    }
	}
	return readBlock(s, createContext(pvs));
    }

    protected void insertToMap(recoder.ModelElement r,
			       ModelElement k) {
	
	if (r != null) {
	    rec2key.put(r, k);
	} else {
	    // commented out because they caused an exception (they were thrown at array references)
// 	    Debug.out("Rec2Key.insertToMap : Omitting entry  (r = " + r + " -> k = " + k + ")");
// 	    Debug.out("Maybe there is a bug !!");
	}
    }

    /**
     * returns the hashmap of a concrete RecodeR class to the constructor of its 
     * corresponding KeY class. Speeds up reflection.
     * Attention must be overwritten by subclasses!
     */
    protected HashMap getKeYClassConstructorCache() {
	return recClass2keyClassCons;
    }

    /**
     * returns the hashmap of a concrete Java AST class to its
     * corresponding convert method. Speeds up reflection.
     * Attention must be overwritten by subclasses!
     */
    protected HashMap getMethodCache() {
	return ct2meth;
    }

    /** determines the right convert method using reflection
     * @param pe the recoder.java.JavaProgramElement to be converted
     * @return the converted element
     */    
    protected Object callConvert(recoder.java.ProgramElement pe) { 

	assert pe != null;


	final HashMap methodCache = getMethodCache();
	final Class contextClass = pe.getClass();
	Method m = (Method) methodCache.get(contextClass);

	if (m == null) {
	    Class[] context = new Class[]{contextClass};

	    final LinkedList l = new LinkedList();
	    while (m == null && context[0]!=null) {	    
		l.add(contextClass);
		try {
		    m = getClass().getMethod("convert", context);
		} catch (NoSuchMethodException nsme) {
		    context[0] = context[0].getSuperclass();
		    Debug.out("recoder2key: method not found. " +
			      "Next try with ", context[0]);		
		}
	    }
            assert m != null : "Could not find convert method";
	    final Iterator it = l.iterator();
	    while (it.hasNext()) {
		methodCache.put(it.next(), m);
	    }
	}

	Object o = null;
	try {
	    o = m.invoke(this, new Object[]{pe});
	} catch (IllegalAccessException iae) {
	    Debug.out("recoder2key: cannot access method ", iae);
	    throw new ConvertException("recoder2key: cannot access method" + iae);
	} catch (IllegalArgumentException iarg) {
	    Debug.out("recoder2key: wrong method arguments ", iarg);
	    throw new ConvertException("recoder2key: wrong method arguments" + iarg);
	} catch (InvocationTargetException ite) {
	    Debug.out("recoder2key: called method threw exception ", 
		      ite.getTargetException());
	    if (ite.getTargetException() instanceof ConvertException) {
		throw (ConvertException)ite.getTargetException();
	    } else {
		//ite.getTargetException().printStackTrace();
		throw new ConvertException
		    ("recoder2key: called method "+ m + " threw exception:" +
		     ite.getTargetException());
	    }
	}

	if ((currentClass != null) && (o instanceof Statement) &&
            ! (o instanceof SchemaVariable)) {
            ((JavaProgramElement)o).setParentClass(currentClass);
	}

	return o;
    }

    /** 
     * constructs the name of the corresponding KeYClass
     * @param recoderClass Class that is the original recoder 
     * @return String containing the KeY-Classname
     */
    protected String getKeYName(Class recoderClass) {
        // value of recoderPrefixLength is: "recoder.".length()
        final int recoderPrefixLength = 8;

        return "de.uka.ilkd.key." + 
            recoderClass.getName().substring(recoderPrefixLength);
    }

    
    /** gets the KeY-Class related to the recoder one
     * @param recoderClass the original Class
     * @return the related KeY Class 
     */
    protected Class getKeYClass(Class recoderClass) {
	try {
	    return Class.forName(getKeYName(recoderClass));
	} catch (ClassNotFoundException cnfe) {
	    Debug.out("There is an AST class missing at KeY.", cnfe);
	    throw new ConvertException
		("There is an AST class missing at KeY. " + cnfe);
	} catch (ExceptionInInitializerError initErr) {
	    Debug.out("recoder2key: Failed initializing class ", initErr);
	    Debug.fail();
	} catch (LinkageError le) {
	    Debug.out("recoder2key: Linking class failed.", le);
	    Debug.fail();
	}
	return null;
    }

    /** determines the right standard constructor of the KeYClass
     * @param recoderClass the Class of the recoder AST object
     * @return the Constructor of the right KeY-Class
     */
    protected Constructor getKeYClassConstructor(Class recoderClass) {
	Constructor result=null;
	try {
	    result = (Constructor)getKeYClassConstructorCache().get(recoderClass);
	    if (result == null) {
		result = getKeYClass(recoderClass).getConstructor
		    (new Class[]{ExtList.class}); 
		getKeYClassConstructorCache().put(recoderClass, result);
	    }	    
	} catch (NoSuchMethodException nsme) {
	    Debug.out("recoder2key: constructor not found. ", nsme);
	} catch (SecurityException se) {
	    Debug.out("recoder2key: access denied. ", se);
	}
	return result;
    }


    /** collects children and adds their converted KeY-counterpart to
     * the list of childrem
     * @param pe the NonTerminalProgramElement that needs its
     * children before being converted
     * @return the list of children after conversion
     */
    protected ExtList collectChildren
	(recoder.java.NonTerminalProgramElement pe) {
	ExtList children = new ExtList();
	for (int i=0, childCount = 
            pe.getChildCount(); i<childCount; i++) {
	    children.add(callConvert(pe.getChildAt(i)));
	}
	recoder.list.CommentList l = pe.getComments();
	if(l!=null){
	    for(int i = 0, sz = l.size(); i < sz; i++){
		children.add(convert(l.getComment(i)));
	    }
	}
	children.add(positionInfo(pe));
	return children;
    }

    /** collects comments and adds their converted KeY-counterpart to
     * the list of childrem
     * @param pe the ProgramElement that needs its
     * comments before being converted
     * @return the list of comments after conversion
     */
    protected ExtList collectComments(recoder.java.ProgramElement pe){
	ExtList children = new ExtList();
	recoder.list.CommentList l = pe.getComments();
	if(l!=null){
	    for(int i=0, sz = l.size(); i<sz; i++){
		children.add(convert(l.getComment(i)));
	    }
	}
	return children;
    }

    protected PositionInfo positionInfo(recoder.java.SourceElement se) {
	Position relPos   = new Position(se.getRelativePosition().getLine(),
				     se.getRelativePosition().getColumn());
	Position startPos = new Position(se.getStartPosition().getLine(),
					 se.getStartPosition().getColumn());
	Position endPos   = new Position(se.getEndPosition().getLine(),
					 se.getEndPosition().getColumn());
	if ((!inLoopInit))
            return new PositionInfo(relPos, startPos, endPos, currentClass);
        else return new PositionInfo(relPos, startPos, endPos);

    }

    /**
     * the standard case. 
     * @param pe the recoder.java.ProgramElement to be converted 
     * @return the converted de.uka.ilkd.key.java.JavaProgramElement 
     */
    public ProgramElement convert(recoder.java.JavaProgramElement pe) {
	ProgramElement result = null;
	ExtList parameter; 

	if (pe instanceof recoder.java.JavaNonTerminalProgramElement) {
	    parameter = 
		collectChildren((recoder.java.JavaNonTerminalProgramElement) pe);
	} else {
	    parameter = new ExtList();
	}
	try {	    
	    result = (ProgramElement) getKeYClassConstructor(pe.getClass()).
		newInstance(new Object[]{parameter});
	} catch (InstantiationException e) {       
	    Debug.out("recoder2key: invocation of constructor failed.", e);
	} catch (InvocationTargetException ite) {       
	    Debug.out("recoder2key: invocation of constructor failed.",
		      ite.getTargetException());
	} catch (IllegalAccessException iae) {       
	    Debug.out("recoder2key: access denied.", iae);
	} catch (IllegalArgumentException iae) {       
	    Debug.out("recoder2key: illegal arguments.", iae);
	}
	return result;
    }


    // ------------------- operators ----------------------
    

    public Instanceof convert
	(recoder.java.expression.operator.Instanceof rio) {       
	return new Instanceof
	    ((Expression)callConvert(rio.getExpressionAt(0)),
	     (TypeReference)callConvert(rio.getTypeReference()));

    }

    /** 
     * converts the passive expression of the recoder extensions
     * to the KeYDependance
     */
    public PassiveExpression convert
	(de.uka.ilkd.key.java.recoderext.PassiveExpression pass){
	return new PassiveExpression(collectChildren(pass));
    }
    
    /** 
     * converts the parenthesized expression to the KeYDependance
     */
    public ParenthesizedExpression convert
	(recoder.java.expression.ParenthesizedExpression x){
	// first we need to collect all children
	Debug.assertTrue
	    (!(x instanceof de.uka.ilkd.key.java.recoderext.PassiveExpression));
	return new ParenthesizedExpression(collectChildren(x));
    }

    /** 
     * converts the recoder.java.Comment to the KeYDependance
     */
    public Comment convert(recoder.java.Comment rc){
        return new Comment(rc.getText(), positionInfo(rc));
    }

    /** 
     * converts the recoder.java.expression.operator.NewArray
     * node to the KeYDependance
     */
    public NewArray convert(recoder.java.expression.operator.NewArray newArr){
	// first we need to collect all children
	ExtList children=collectChildren(newArr);
	// now we have to extract the array initializer
	// is stored separately and must not appear in the children list
	ArrayInitializer arrInit=(ArrayInitializer)
	    children.get(ArrayInitializer.class);
	children.remove(arrInit);	
		
	recoder.abstraction.Type javaType = servConf.
	    getCrossReferenceSourceInfo().getType(newArr);

	return new NewArray(children, getKeYJavaType(javaType), arrInit, 
			    newArr.getDimensions());
    }

    /** 
     * converts the recoder.java.expression.operator.CopyAssignment
     * node to the KeYDependance
     */
    public CopyAssignment convert(recoder.java.expression.operator.CopyAssignment ass){	
	return new CopyAssignment(collectChildren(ass));
    }
    
    /** 
     * converts the de.uka.ilkd.key.recoderext.java.expression.operator.SetAssignment
     * node to the KeYDependance
     */
    public SetAssignment convert(de.uka.ilkd.key.java.recoderext.SetAssignment ass){ 
        return new SetAssignment(collectChildren(ass));
    }

    /** 
     * converts the recoder.java.expression.operator.PostIncrement
     * node to the KeYDependance
     */
    public PostIncrement convert
	(recoder.java.expression.operator.PostIncrement postInc) {
	return new PostIncrement(collectChildren(postInc));
    }

    /** 
     * converts the recoder.java.expression.operator.PreIncrement
     * node to the KeYDependance
     */
    public PreIncrement convert
	(recoder.java.expression.operator.PreIncrement preInc){
	return new PreIncrement(collectChildren(preInc));
    }

    /** 
     * converts the recoder.java.expression.operator.PostDecrement
     * node to the KeYDependance
     */
    public PostDecrement convert
	(recoder.java.expression.operator.PostDecrement postDec) {
	return new PostDecrement(collectChildren(postDec));
    }

    /** 
     * converts the recoder.java.expression.operator.PreDecrement
     * node to the KeYDependance
     */
    public PreDecrement convert
	(recoder.java.expression.operator.PreDecrement preDec){		
	return new PreDecrement(collectChildren(preDec));
    }

    /** 
     * converts the recoder.java.expression.operator.Minus
     * node to the KeYDependance
     */
    public Minus convert
	(recoder.java.expression.operator.Minus minus){		
	return new Minus(collectChildren(minus));
    }


    /** 
     * converts the recoder.java.expression.operator.Plus
     * node to the KeYDependance
     */
    public Plus convert
	(recoder.java.expression.operator.Plus plus){	
	return new Plus(collectChildren(plus));
    }

    /** 
     * converts the recoder.java.expression.operator.Times
     * node to the KeYDependance
     */
    public Times convert
	(recoder.java.expression.operator.Times times){	
	return new Times(collectChildren(times));
    }

    /** 
     * converts the recoder.java.expression.operator.Divide
     * node to the KeYDependance
     */
    public Divide convert
	(recoder.java.expression.operator.Divide div){
        return new Divide(collectChildren(div));
    }


    /** 
     * converts the recoder.java.expression.operator.PlusAssignment
     * node to the KeYDependance
     */
    public PlusAssignment convert
	(recoder.java.expression.operator.PlusAssignment plus){	
	return new PlusAssignment(collectChildren(plus));
    }

    /** 
     * converts the recoder.java.expression.operator.MinusAssignment
     * node to the KeYDependance
     */
    public MinusAssignment convert
	(recoder.java.expression.operator.MinusAssignment minus){
	return new MinusAssignment(collectChildren(minus));
    }

    /** 
     * converts the recoder.java.expression.operator.TimesAssignment
     * node to the KeYDependance
     */
    public TimesAssignment convert
	(recoder.java.expression.operator.TimesAssignment times){
	return new TimesAssignment(collectChildren(times));
    }

    /** 
     * converts the recoder.java.expression.operator.DivideAssignment
     * node to the KeYDependance
     */
    public DivideAssignment convert
	(recoder.java.expression.operator.DivideAssignment div){	
	return new DivideAssignment(collectChildren(div));
    }

    /** 
     * converts the recoder.java.expression.operator.LessThan
     * node to the KeYDependance
     */
    public LessThan convert
	(recoder.java.expression.operator.LessThan op){
	return new LessThan(collectChildren(op));
    }

    /** 
     * converts the recoder.java.expression.operator.LessOrEquals
     * node to the KeYDependance
     */
    public LessOrEquals convert
	(recoder.java.expression.operator.LessOrEquals op){	
	return new LessOrEquals(collectChildren(op));
    }

    /** 
     * converts the recoder.java.expression.operator.GreaterThan
     * node to the KeYDependance
     */
    public GreaterThan convert
	(recoder.java.expression.operator.GreaterThan op){
	return new GreaterThan(collectChildren(op));
    }

    /** 
     * converts the recoder.java.expression.operator.GreaterOrEquals
     * node to the KeYDependance
     */
    public GreaterOrEquals convert
	(recoder.java.expression.operator.GreaterOrEquals op){
	return new GreaterOrEquals(collectChildren(op));
    }

    /** 
     * converts the recoder.java.expression.operator.Equals
     * node to the KeYDependance
     */
    public Equals convert
	(recoder.java.expression.operator.Equals op){
	return new Equals(collectChildren(op));
    }

    /** 
     * converts the recoder.java.expression.operator.NotEquals
     * node to the KeYDependance
     */
    public NotEquals convert
	(recoder.java.expression.operator.NotEquals op){
	return new NotEquals(collectChildren(op));
    }


    /** 
     * converts the recoder.java.expression.operator.LogicalNot
     * node to the KeYDependance
     */
    public LogicalNot convert
	(recoder.java.expression.operator.LogicalNot op){
	return new LogicalNot(collectChildren(op));
    }

    /** 
     * converts the recoder.java.expression.operator.LogicalAnd
     * node to the KeYDependance
     */
    public LogicalAnd convert
	(recoder.java.expression.operator.LogicalAnd op){
	return new LogicalAnd(collectChildren(op));
    }

    /** 
     * converts the recoder.java.expression.operator.LogicalOr
     * node to the KeYDependance
     */
    public LogicalOr convert
	(recoder.java.expression.operator.LogicalOr op){
	return new LogicalOr(collectChildren(op));
    }

    /** convert a recoder ArrayInitializer to a KeY array initializer*/    
    public ArrayInitializer convert(recoder.java.expression.ArrayInitializer ai) {
	return new ArrayInitializer(collectChildren(ai));
    }
    
    //------------------- literals --------------------------------------
    

    /** convert a recoder IntLiteral to a KeY IntLiteral */
    public IntLiteral convert
	(recoder.java.expression.literal.IntLiteral intLit) {
	// if there are comments to take into consideration 
	// change parameter to ExtList
	return new IntLiteral(intLit.getValue());
    }
    
    /** convert a recoder BooleanLiteral to a KeY BooleanLiteral */
    public BooleanLiteral 
	convert(recoder.java.expression.literal.BooleanLiteral booleanLit) {

	// if there are comments to take into consideration 
	// change parameter to ExtList
	return (booleanLit.getValue() ? BooleanLiteral.TRUE : BooleanLiteral.FALSE);
    }


    /** convert a recoder StringLiteral to a KeY StringLiteral */
    public StringLiteral 
	convert(recoder.java.expression.literal.StringLiteral stringLit) {

	// if there are comments to take into consideration 
	// change parameter to ExtList
	return new StringLiteral(stringLit.getValue());
    }

    /** convert a recoder DoubleLiteral to a KeY DoubleLiteral */
    public DoubleLiteral 
	convert(recoder.java.expression.literal.DoubleLiteral doubleLit) {

	// if there are comments to take into consideration 
	// change parameter to ExtList
	return new DoubleLiteral(doubleLit.getValue());
    }

    /** convert a recoder FloatLiteral to a KeY FloatLiteral */
    public FloatLiteral 
	convert(recoder.java.expression.literal.FloatLiteral floatLit) {

	// if there are comments to take into consideration 
	// change parameter to ExtList
	return new FloatLiteral(floatLit.getValue());
    }

    /** convert a recoder LongLiteral to a KeY LongLiteral */
    public LongLiteral 
	convert(recoder.java.expression.literal.LongLiteral longLit) {

	// if there are comments to take into consideration 
	// change parameter to ExtList
	return new LongLiteral(longLit.getValue());
    }

    /** convert a recoder CharLiteral to a KeY CharLiteral */
    public CharLiteral 
	convert(recoder.java.expression.literal.CharLiteral charLit) {

	// if there are comments to take into consideration 
	// change parameter to ExtList

	return new CharLiteral(charLit.getValue());
    }


    /** convert a recoder NullLiteral to a KeY NullLiteral */
    public NullLiteral 
	convert(recoder.java.expression.literal.NullLiteral nullLit) {

	recoder.abstraction.Type javaType = getServiceConfiguration().
	    getCrossReferenceSourceInfo().getType(nullLit);
	getKeYJavaType(javaType);
	// if there are comments to take into consideration 
	// change parameter to ExtList
	return NullLiteral.NULL;
    }



    //----------------------------------------------------------

    
    /** convert a recoder EmptyStatement to a KeY EmptyStatement*/
    public EmptyStatement convert(recoder.java.statement.EmptyStatement
				       eStmnt) {	
	// may change if comments are implemented, then 
	// new EmptyStatement(children);
	return new EmptyStatement();
    }

    /** converts a recoder throw statement to a KeY throw statement*/
    public Throw convert(recoder.java.statement.Throw stmntThrow) {	
	return new Throw(collectChildren(stmntThrow));
    }

    /** converts a recoder if statement to a KeY if statement*/
    public If convert(recoder.java.statement.If stmntIf) {	
	return new If(collectChildren(stmntIf));
    }

    /** converts a recoder then statement to a KeY then statement*/
    public Then convert(recoder.java.statement.Then stmntThen) {	
	return new Then(collectChildren(stmntThen));
    }

    /** converts a recoder else statement to a KeY else statement*/
    public Else convert(recoder.java.statement.Else stmntElse) {	
	return new Else(collectChildren(stmntElse));
    }
	
    /** convert a recoder EmptyStatement to a KeY EmptyStatement*/    
    public ProgramElementName convert(recoder.java.Identifier id) {
	return VariableNamer.parseName(id.getText(),
				      (Comment[]) collectComments(id).
				      collect(Comment.class));
    }

    /** convert a recoder EmptyStatement to a KeY EmptyStatement*/
    public ProgramElementName convert(ImplicitIdentifier id) {

	return new ProgramElementName(id.getText(),
				      (Comment[]) collectComments(id).
				      collect(Comment.class));
    }

    /** convert a recoder StamentBlock to a KeY StatementBlock*/
    public StatementBlock convert(recoder.java.StatementBlock block) {
	return new StatementBlock(collectChildren(block));
    }
    
    /** convert a recoder StamentBlock to a KeY StatementBlock*/    
    public SynchronizedBlock convert(recoder.java.statement.SynchronizedBlock block) {
	return new SynchronizedBlock(collectChildren(block));
    }

    /** convert a recoder return statement to a KeY return statement */
    public Return convert(recoder.java.statement.Return stmntReturn) {
	return new Return(collectChildren(stmntReturn));
    }

    /** convert a recoder try statement to a KeY try statement */    
    public Try convert(recoder.java.statement.Try stmntTry) {
	return new Try(collectChildren(stmntTry));
    }

    /** convert a recoder catch statement to a KeY catch statement */    
    public Catch convert(recoder.java.statement.Catch stmntCatch) {
	return new Catch(collectChildren(stmntCatch));
    }

    /** convert a recoder finally statement to a KeY finally statement */    
    public Finally convert(recoder.java.statement.Finally stmntFinally) {
	return new Finally(collectChildren(stmntFinally));
    }
    
    /** convert a recoderext MethodFrameStatement to a KeY MethodFrameStatement*/
    public MethodFrame 
	convert(de.uka.ilkd.key.java.recoderext.MethodCallStatement rmcs) {
        ProgramVariable resVar = null;
        if (rmcs.getResultVariable() != null) {
            recoder.java.Expression rvar = rmcs.getResultVariable();
            if (rvar instanceof recoder.java.reference.VariableReference) {
                resVar = convert((recoder.java.reference.VariableReference)rvar);
            } else if (rvar instanceof recoder.java.reference.UncollatedReferenceQualifier) {
                try {
                    resVar = (ProgramVariable)callConvert(rvar);
                } catch (ClassCastException e) {
                    throw new ConvertException("recoder2key: Expression is not a variable reference.");
                }
            }
        }
        StatementBlock block = null;
        if (rmcs.getBody() != null) {
            block = (StatementBlock) callConvert(rmcs.getBody());
        }

        return new MethodFrame(resVar, 
			       convert(rmcs.getExecutionContext()),
			       block);
    }

    /** convert a recoderext MethodBodyStatement to a KeY MethodBodyStatement*/
    public MethodBodyStatement convert
	(de.uka.ilkd.key.java.recoderext.MethodBodyStatement rmbs) {       
        
        final TypeReference bodySource = convert(rmbs.getBodySource());
        final IProgramVariable resultVar = rmbs.getResultVariable() != null ?
                (IProgramVariable)callConvert(rmbs.getResultVariable()) : null;
        final ReferencePrefix invocationTarget = (ReferencePrefix) 
            callConvert(rmbs.getReferencePrefix());        
        final ProgramElementName methodName = convert(rmbs.getMethodName());
       
        final ExpressionMutableList args = rmbs.getArguments(); 
        final Expression[] keyArgs;
        if (args != null) {
            keyArgs = new Expression[args.size()];
            for (int i = 0, sz = args.size(); i<sz; i++) {
                keyArgs[i] = (Expression) callConvert(args.getExpression(i));           
            }
        } else {
            keyArgs = new Expression[0];
        }                
        
        final MethodReference mr = 
            new MethodReference(new ArrayOfExpression(keyArgs), 
                    methodName, invocationTarget);
        
        return new MethodBodyStatement(bodySource, resultVar, mr);
    }

    public CatchAllStatement convert
	(de.uka.ilkd.key.java.recoderext.CatchAllStatement cas) {
	return new CatchAllStatement
	    ((StatementBlock)callConvert(cas.getStatementAt(0)), 
	     (ParameterDeclaration) callConvert(cas.getParameterDeclarationAt(0)));
    }


    // ------------------- modifiers ----------------------
    
    /**
     * converts the recoder public modifier to the KeY modifier
     */
    public Public convert(recoder.java.declaration.modifier.Public m) {
	return new Public(collectComments(m));
    }
   

    /**
     * converts the recoder protected modifier to the KeY modifier
     */
    public Protected convert(recoder.java.declaration.modifier.Protected m) {
	return new Protected(collectComments(m));
    }

    /**
     * converts the recoder private modifier to the KeY modifier
     */
    public Private convert(recoder.java.declaration.modifier.Private m) {
	return new Private(collectComments(m));
    }

    /**
     * converts the recoder static modifier to the KeY modifier
     */
    public Static convert(recoder.java.declaration.modifier.Static m) {
	return new Static(collectComments(m));
    }

    /**
     * converts the recoder abstract modifier to the KeY modifier
     */
    public Abstract convert(recoder.java.declaration.modifier.Abstract m) {
	return new Abstract(collectComments(m));
    }

    
    /**
     * converts the recoder final modifier to the KeY modifier
     */
    public Final convert(recoder.java.declaration.modifier.Final m) {
	return new Final(collectComments(m));
    }
    /**
     * converts the recoder native modifier to the KeY modifier
     */
    public Native convert(recoder.java.declaration.modifier.Native m) {
	return new Native(collectComments(m));
    }
        
    /**
     * converts the recoder transient modifier to the KeY modifier
     */
    public Transient convert(recoder.java.declaration.modifier.Transient m) {
	return new Transient(collectComments(m));
    }
    
    /**
     * converts the recoder synchronized modifier to the KeY modifier
     */
    public Synchronized convert(recoder.java.declaration.modifier.Synchronized m) {
	return new Synchronized(collectComments(m));
    }

    /**
     * converts the recoder ghost modifier to the KeY modifier
     */
    public Ghost convert(de.uka.ilkd.key.java.recoderext.Ghost m) {
        return new Ghost(collectComments(m));
    }
    
    /**
     * converts the recoder model modifier to the KeY modifier
     */
    public Model convert(de.uka.ilkd.key.java.recoderext.Model m) {
        return new Model(collectComments(m));
    }

    //------------------- declaration ---------------------
   
    public CompilationUnit convert(recoder.java.CompilationUnit cu) {
        return new CompilationUnit(collectChildren(cu));
    }
   
    public ClassInitializer convert(recoder.java.declaration.ClassInitializer ci) {
        return new ClassInitializer(collectChildren(ci));
    }
    
    public PackageSpecification convert(recoder.java.PackageSpecification ps) {
        return new PackageSpecification(collectChildren(ps));
    }
    
    public Throws convert(recoder.java.declaration.Throws t) {
        return new Throws(collectChildren(t));
    }

    public Extends convert(recoder.java.declaration.Extends e) {
        return new Extends(collectChildren(e));
    }
    
    public Implements convert(recoder.java.declaration.Implements e) {
        return new Implements(collectChildren(e));
    }
            
    public ClassDeclaration convert
	(recoder.java.declaration.ClassDeclaration td) {

	KeYJavaType kjt = getKeYJavaType(td);
	ExtList classMembers = collectChildren(td);       

	ClassDeclaration keYClassDecl = new ClassDeclaration
	    (classMembers,
	     new ProgramElementName(td.getFullName()),
	     parsingLibs);


	kjt.setJavaType(keYClassDecl);
	return keYClassDecl;	
    }
            
    public InterfaceDeclaration convert
	(recoder.java.declaration.InterfaceDeclaration td) {


	KeYJavaType kjt =  getKeYJavaType(td);
	ExtList members = collectChildren(td);       
	InterfaceDeclaration keYInterfaceDecl
	    = new InterfaceDeclaration
	    (members, new ProgramElementName(td.getFullName()), parsingLibs);
	kjt.setJavaType(keYInterfaceDecl);

	return keYInterfaceDecl;	
    }

    
        
    /** 
     * converts a recoder LocalVariableDeclaration to a KeY
     * LocalVariableDeclaration
     * (especially the declaration type of its parent is determined
     * and handed over)
     */
    public LocalVariableDeclaration
	convert(recoder.java.declaration.LocalVariableDeclaration lvd) {	
        return new LocalVariableDeclaration(collectChildren(lvd)); 
    }


    /** 
     * converts a recoder ParameterDeclaration to a KeY
     * ParameterDeclaration
     * (especially the declaration type of its parent is determined
     * and handed over)
     */
    public ParameterDeclaration
	convert(recoder.java.declaration.ParameterDeclaration pd) {    
	return new ParameterDeclaration
	    (collectChildren(pd), pd.getASTParent() 
	     instanceof recoder.java.declaration.InterfaceDeclaration); 
    }


     /** convert a recoder FieldDeclaration to a KeY
      * FieldDeclaration
      * (especially the declaration type of its parent is determined
      * and handed over)
      */
     public FieldDeclaration
 	convert(recoder.java.declaration.FieldDeclaration fd) {    
	 return new FieldDeclaration
	     (collectChildren(fd), fd.getASTParent()
	      instanceof recoder.java.declaration.InterfaceDeclaration);
     }

     /** convert a recoder ConstructorDeclaration to a KeY
      * ProgramMethod
      * (especially the declaration type of its parent is determined
      * and handed over)
      */
     public ProgramMethod
     convert(recoder.java.declaration.ConstructorDeclaration cd) {    
    	 ConstructorDeclaration consDecl = new ConstructorDeclaration
    	 (collectChildren(cd), cd.getASTParent() instanceof
    			 recoder.java.declaration.InterfaceDeclaration);
    	 recoder.abstraction.ClassType cont = 
    		 servConf.getCrossReferenceSourceInfo().
    		 getContainingClassType((recoder.abstraction.Member)cd);
    	 
    	 ProgramMethod result = 
	     new ProgramMethod(consDecl, getKeYJavaType(cont),
			       getKeYJavaType(cd.getReturnType()),
			       positionInfo(cd));
    	 insertToMap(cd, result);
    	 return result;
     }

     /** convert a recoder DefaultConstructor to a KeY
      * ProgramMethod
      * (especially the declaration type of its parent is determined
      * and handed over)
      */
     public ProgramMethod convert(recoder.abstraction.DefaultConstructor dc) {
	 ExtList children = new ExtList();
	 children.add(new ProgramElementName(dc.getName()));
    	 ConstructorDeclaration consDecl = new ConstructorDeclaration
    	 (children, dc.getContainingClassType().isInterface());
    	 recoder.abstraction.ClassType cont = dc.getContainingClassType();
    	 ProgramMethod result = 
	     new ProgramMethod(consDecl, getKeYJavaType(cont), 
			       getKeYJavaType(dc.getReturnType()), 
			       PositionInfo.UNDEFINED);
    	 insertToMap(dc, result);
    	 return result;
     }

    public TypeCast
	convert(recoder.java.expression.operator.TypeCast c) {
	return new TypeCast
	    ((Expression)callConvert(c.getExpressionAt(0)), 
	     (TypeReference)callConvert(c.getTypeReference()));	
    }

    private KeYJavaType lookup(recoder.abstraction.Type t) {
	return (KeYJavaType) rec2key.toKeY(t);
    }
    
    private boolean isObject(recoder.abstraction.ClassType ct) {
	return "java.lang.Object".equals(ct.getFullName())
	    || "Object".equals(ct.getName());
    }

    private Sort createObjectSort(recoder.abstraction.ClassType ct, 
				  SetOfSort supers) {
        final boolean abstractOrInterface = ct.isAbstract() ||
            ct.isInterface();
        return new ClassInstanceSortImpl(new Name(ct.getFullName()), 
					 supers, abstractOrInterface);
    }

    private SetOfSort directSuperSorts
	(recoder.abstraction.ClassType classType) {

	recoder.list.ClassTypeList supers=classType.getSupertypes();
	SetOfSort ss=SetAsListOfSort.EMPTY_SET;
	for (int i=0; i<supers.size(); i++) {
	    ss = ss.add(getKeYJavaType(supers.getClassType(i)).getSort());	    
	}

	if (ss==SetAsListOfSort.EMPTY_SET && !isObject(classType)) {
	    ss=ss.add(javaInfo().getJavaLangObjectAsSort());
	}
	return ss;
    }

    private KeYJavaType getKeYJavaType(recoder.abstraction.Type t) {		
	if (t == null) {
	    return null; //this can originate from 'void'
	}
	KeYJavaType kjt = lookup(t);
	
	if (kjt != null) {
	    return kjt;
	}
	// create a new KeYJavaType
	Sort s = null;
	if (t instanceof recoder.abstraction.PrimitiveType) {
	    s = typeConverter.getPrimitiveSort
		(PrimitiveType.getPrimitiveType(t.getFullName()));
	    if (s==null) {
		s=new PrimitiveSort(new Name(t.getFullName()));
		namespaces.sorts().add(s);
		Debug.out("create primitive sort not backed by LDT",s);
	    }
	    addKeYJavaType(t, s);
	} else if (t instanceof recoder.abstraction.NullType) {
	    s = Sort.NULL;
	    addKeYJavaType(t, s);
	} else if (t instanceof recoder.abstraction.ClassType) {
	    recoder.abstraction.ClassType ct=(recoder.abstraction.ClassType)t;
	    if (ct.isInterface()){
		s = createObjectSort(ct, directSuperSorts(ct).
				     add(javaInfo().getJavaLangObjectAsSort()));
	    }else{
		s = createObjectSort(ct, directSuperSorts(ct));
	    }
	    recoder.list.ConstructorList cl = 
		t.getProgramModelInfo().
		getConstructors((recoder.abstraction.ClassType) t);
	    addKeYJavaType(t, s);
	    if(cl.size()==1 && 
	       (cl.getConstructor(0) instanceof 
		recoder.abstraction.DefaultConstructor)){
		convert((recoder.abstraction.DefaultConstructor) 
			cl.getConstructor(0));
	    }
	} else if (t instanceof recoder.abstraction.ArrayType){
	    recoder.abstraction.Type bt
		= ((recoder.abstraction.ArrayType)t).getBaseType();                                 
            
            kjt = getKeYJavaType(bt);
            
	    s = ArraySortImpl.getArraySort(kjt.getSort(),
					   javaInfo().getJavaLangObjectAsSort(),
					   javaInfo().getJavaLangCloneableAsSort(),
                                           javaInfo().getJavaIoSerializableAsSort());	             
            addKeYJavaType(t, s);
        }
	return lookup(t);
    }

    private KeYJavaType addKeYJavaType(recoder.abstraction.Type t, Sort s) {
	KeYJavaType result = null;
	if (!(t instanceof recoder.java.declaration.TypeDeclaration)) {
	    Type type = null;
	    if (t instanceof recoder.abstraction.PrimitiveType) {
		type = PrimitiveType.getPrimitiveType(t.getFullName());
		result = typeConverter.getKeYJavaType(type);
		if (result == null) {
		    Debug.out("recoder2key: create new KeYJavaType for", t);
		    Debug.out("recoder2key: this should not happen");
		    result = new KeYJavaType(type, s);
		}
	    } else if (t instanceof recoder.abstraction.NullType) {
		type = NullType.JAVA_NULL;
                if (namespaces.sorts ().lookup(s.name()) == null) {
		    setUpSort(s);
		}
                result = new KeYJavaType(type, s);
	    } else if (t instanceof ClassFile) {
                    setUpSort(s);     
                    result = new KeYJavaType(s);    
                    insertToMap(t, result);                  
                    type = createTypeDeclaration((ClassFile)t);		    
                    
                    return (KeYJavaType) rec2key.toKeY(t);                                
	    } else if (t instanceof recoder.abstraction.ArrayType) {
		setUpSort(s);
		result = new KeYJavaType(s);
	    } else {
		Debug.out("recoder2key: unknown type", t);
		Debug.fail();
		result = new KeYJavaType();
	    }
	} else {
	    setUpSort ( s );
	    result = new KeYJavaType(s);
	}
	insertToMap(t, result);


	// delayed creation of virtual array declarations
	// to avoid cycles
	if (t instanceof recoder.abstraction.ArrayType) {
	    result.setJavaType
		(createArrayType(getKeYJavaType
		  (((recoder.abstraction.ArrayType)t).getBaseType()),
		  (KeYJavaType)rec2key.toKeY(t)));
	}

	return (KeYJavaType) rec2key.toKeY(t); //usually this equals result,
	//sometimes however, there is a 'legacy' type in the mapping,
	//which has priority
    }
    
  
    private TypeDeclaration createTypeDeclaration(ClassFile cf) {     
        final KeYJavaType classType = getKeYJavaType(cf);

        final Modifier[] modifiers = getModifiers(cf);   
        final ProgramElementName name = new ProgramElementName(cf.getName());
        final ProgramElementName fullname = new ProgramElementName(cf.getFullName());
                
        ClassTypeList supertype = cf.getSupertypes();
        
        TypeReference[] implementsTypes = null;
        TypeReference extendType        = null;
        
        LinkedList implementsList = new LinkedList();
        if (supertype != null ) {
            for (int i = 0; i<supertype.size(); i++) {
                recoder.abstraction.ClassType ct = supertype.getClassType(i);
                final KeYJavaType kjt = getKeYJavaType(ct);    
                final TypeReference tr = new TypeRef
                (new ProgramElementName(ct.getFullName()), 0, null, kjt);
                if (ct.isInterface()) {                                                      
                    implementsList.add(tr);
                } else {                   
                    Debug.assertTrue(extendType == null);                        
                    extendType = tr;                       
                }
            }
            implementsTypes = 
                (TypeReference[])implementsList.
                toArray(new TypeReference[implementsList.size()]);
        }
        
        
        final Extends ext = (extendType == null ? null : new Extends(extendType));
        
        final Implements impl = implementsTypes == null ? null : 
            new Implements(implementsTypes);
        
        
        
        final boolean parentIsInterface = cf.getContainingClassType()!=null ?
                cf.getContainingClassType().isInterface() : false;
                
//              for the moment no members
                
       MemberDeclaration[] members = new MemberDeclaration[0];
             
       
       TypeDeclaration td;
       if (cf.isInterface()) {
           td = new InterfaceDeclaration(modifiers, name, fullname, ext,
                    members, true);
       } else {
           td = new ClassDeclaration(modifiers, name, ext, fullname, impl, members,
                   parentIsInterface, true);
       }
       classType.setJavaType(td);
       return td;
    }

    /**
     * retrieve the modiefiers of <tt>cf</tt> 
     * @param cf the ByteCodeElement whose modifiers are determined
     * @return cf's modifiers 
     */
    private Modifier[] getModifiers(recoder.bytecode.ByteCodeElement cf) {
        LinkedList mods = new LinkedList();
        if (cf.isNative()) {
            mods.add(new Native());
        }
        if (cf.isAbstract()) {
            mods.add(new Abstract());            
        }        
        if (cf.isPublic()) {
            mods.add(new Public());
        } else if (cf.isPrivate()) {
            mods.add(new Private());
        } else if (cf.isProtected()) {
            mods.add(new Protected());
        } 
        if (cf.isFinal()) {
            mods.add(new Final());
        }
        if (cf.isSynchronized()) {
            mods.add(new Synchronized());
        }
        return (Modifier[]) mods.toArray(new Modifier[mods.size()]);
    }


    /**
     * Insert sorts into the namespace, add symbols that may have been
     * defined by a sort to the function namespace (e.g. functions for
     * collection sorts)
     */
    protected void setUpSort ( Sort s ) {
	namespaces.sorts ().add(s);
	if (s instanceof NonCollectionSort) {
	    NonCollectionSort ns
		= (NonCollectionSort)s;
	    namespaces.sorts ().add(ns.getSetSort());
	    namespaces.sorts ().add(ns.getSequenceSort());
	    namespaces.sorts ().add(ns.getBagSort());
	}
	if ( s instanceof SortDefiningSymbols ) {
	    ((SortDefiningSymbols)s).addDefinedSymbols ( namespaces.functions (),
						         namespaces.sorts () );
	}
    }

    // ----------------- references ----------------------------------- //

    /**
     * converts an execution context
     */
    public ExecutionContext 
	convert(de.uka.ilkd.key.java.recoderext.ExecutionContext ec) {

	return new ExecutionContext(collectChildren(ec));
	
    }

    /**
     * converts a recoder this  constructor reference.
     * @return the this reference in the KeY data structures
     */
     public ThisConstructorReference convert
	 (recoder.java.reference.ThisConstructorReference tcr) {	 

	 return new ThisConstructorReference(collectChildren(tcr));
     }


    /**
     * converts a SpecialConstructorReference. 
     * Special handling because the initializing
     * Expressions and the ReferencePrefix accessPath might not be disjunct.
     */
    public SuperConstructorReference 
	convert(recoder.java.reference.SuperConstructorReference scr) {

	ExtList children = collectChildren(scr);
	ReferencePrefix prefix = null;
	int prefixPos=scr.getIndexOfChild(scr.getReferencePrefix());	     
	if (prefixPos!=-1) {
	    prefix=(ReferencePrefix)children.get(prefixPos);
	    children.remove(prefixPos);
	}
	return new SuperConstructorReference(children, prefix);
    }

    public ThisReference 
	convert(recoder.java.reference.ThisReference tr) {
        
	 ExtList children       = collectChildren(tr);
	 ReferencePrefix prefix = null;

	 int prefixPos=tr.getIndexOfChild(tr.getReferencePrefix());	     
	 if (prefixPos != -1) {
	     prefix=(ReferencePrefix)children.get(prefixPos);
	     children.remove(prefixPos);
	 }	 
	 return new ThisReference((TypeReference)prefix);
    }


    public SuperReference 
	convert(recoder.java.reference.SuperReference sr) {	
	
	 ExtList children=collectChildren(sr);	
	 
         int prefixPos=sr.getIndexOfChild(sr.getReferencePrefix());	     
	 if (prefixPos!=-1) {	     
	     children.remove(prefixPos);
	 }
	 
         return new SuperReference(children);
    }


    /** convert a recoder VariableSpecification to a KeY
     * VariableSpecification
     * (checks dimension and hands it over and insert in hashmap)
     */
    public VariableSpecification
	convert(recoder.java.declaration.VariableSpecification recoderVarSpec){

	VariableSpecification varSpec
	    = (VariableSpecification)rec2key.toKeY(recoderVarSpec);
             

	if (varSpec == null) {
	    recoder.abstraction.Type recoderType =
		(servConf.getSourceInfo()).getType(recoderVarSpec);

	    final ProgramElementName name = VariableNamer.
                parseName(recoderVarSpec.getName());
	    final ProgramVariable pv = new LocationVariable(name,
	            getKeYJavaType(recoderType));	   
	    varSpec = new VariableSpecification
		(collectChildren(recoderVarSpec), pv, 
                 recoderVarSpec.getDimensions(),
		 pv.getKeYJavaType());

	    insertToMap(recoderVarSpec, varSpec);
	}
	return varSpec;
    }


    /** convert a recoder MethodDeclaration to a KeY
     * ProgramMethod
     * (especially the declaration type of its parent is determined
     * and handed over)
     */
    public ProgramMethod
	convert(recoder.java.declaration.MethodDeclaration md) {
	ProgramMethod result=null;

	// methodsDeclaring contains the recoder method declarations as keys 
	// that have been started to convert but are not yet finished.
	// The mapped value is the reference to the later completed 
	// ProgramMethod.
	if (methodsDeclaring.containsKey(md)) {
	    // a recursive call from a method reference
	    return (ProgramMethod) methodsDeclaring.get(md);
	                                    //reference that will later be set.
	} 
	methodsDeclaring.put(md, result);
	if (!rec2key.mapped(md)) {
	    final MethodDeclaration methDecl
		= new MethodDeclaration
		    (collectChildren(md), 
                     md.getASTParent() 
                     instanceof recoder.java.declaration.InterfaceDeclaration);
	    recoder.abstraction.ClassType cont = 
		servConf.getCrossReferenceSourceInfo().
		getContainingClassType((recoder.abstraction.Member)md);
	           
	    result = new ProgramMethod
		(methDecl, getKeYJavaType(cont), 
                 getKeYJavaType(md.getReturnType()), positionInfo(md));
	    
            insertToMap(md, result);
	}
	methodsDeclaring.remove(md);
	result = (ProgramMethod)rec2key.toKeY(md);
	return result;
    }


    /** 
     * convert a recoder FieldSpecification to a KeY FieldSpecification
     * (checks dimension and hands it over and insert in hash map)
     */
    public FieldSpecification
 	convert(recoder.java.declaration.FieldSpecification recoderVarSpec){

	if (recoderVarSpec == null) { //%%%%%%%%%%%%%	   
            return new FieldSpecification();
	}

	FieldSpecification varSpec
	    = (FieldSpecification)rec2key.toKeY(recoderVarSpec);

	if (varSpec==null) {
	    recoder.abstraction.Type recoderType =
		(servConf.getSourceInfo()).getType(recoderVarSpec);

	    ProgramVariable pv =
		getProgramVariableForFieldSpecification ( recoderVarSpec );

	    if (recoderVarSpec.getIdentifier() instanceof ImplicitIdentifier) {
		// the modelled field is an implicit one, we have to handle this one
		// explicit 
		varSpec = new ImplicitFieldSpecification
		    (pv, getKeYJavaType(recoderType));
	    } else {	    
		varSpec = new FieldSpecification
		    (collectChildren(recoderVarSpec), 
		     pv,
		     recoderVarSpec.getDimensions(), 
		     getKeYJavaType(recoderType));
	    }
	    insertToMap(recoderVarSpec, varSpec); 
	}

	return varSpec;
    }


    protected ProgramVariable getProgramVariableForFieldSpecification
	( recoder.java.declaration.FieldSpecification recoderVarSpec ) {

	if (recoderVarSpec == null) { //%%%%%%%%%%%%%            
            return null;
        }
	
	ProgramVariable pv =
	    (ProgramVariable)fieldSpecificationMapping.get ( recoderVarSpec );

	if (pv == null) {
	    VariableSpecification varSpec = (VariableSpecification) rec2key
		.toKeY(recoderVarSpec);
	    if (varSpec == null) {
		recoder.abstraction.Type recoderType = 
		    (servConf.getSourceInfo()).getType(recoderVarSpec);
		final ClassType recContainingClassType = 
		    recoderVarSpec.getContainingClassType();
		final ProgramElementName pen = 
		    new ProgramElementName(recoderVarSpec.getName(),
		            recContainingClassType.getFullName());		
		
                                
                final Literal compileTimeConstant = 
                    getCompileTimeConstantInitializer(recoderVarSpec);
                
                
                if (compileTimeConstant == null) {
                    pv = new LocationVariable(pen, getKeYJavaType(recoderType),
                            getKeYJavaType(recContainingClassType), 
                            recoderVarSpec.isStatic());
                } else {
                    pv = new ProgramConstant(pen, getKeYJavaType(recoderType), 
                            getKeYJavaType(recContainingClassType),
                            recoderVarSpec.isStatic(), compileTimeConstant);
                }
	    } else {
		pv = (ProgramVariable) varSpec.getProgramVariable();
	    }
	    fieldSpecificationMapping.put(recoderVarSpec, pv);
	}

	return pv;
    }


    /**
     * @return a literal constant representing the value of the
     * initializer of <code>recoderVarSpec</code>, if the variable is
     * a compile-time constant, and <code>null</code> otherwise
     */
    private Literal getCompileTimeConstantInitializer
	( recoder.java.declaration.FieldSpecification recoderVarSpec ) {

	// Necessary condition: the field is static and final
	if ( !recoderVarSpec.isFinal () || !recoderVarSpec.isStatic () )
	    return null;

	recoder.java.Expression init = recoderVarSpec.getInitializer ();

	if ( init != null ) {
	    recoder.service.ConstantEvaluator                  ce =
		new recoder.service.DefaultConstantEvaluator
		( getServiceConfiguration () );
	    recoder.service.ConstantEvaluator.EvaluationResult er =
		new recoder.service.ConstantEvaluator.EvaluationResult ();
	
	    if ( ce.isCompileTimeConstant ( init, er ) )
		return getLiteralFor ( er );
	}

	return null;
    }

  /**
     * @return a literal constant representing the value of
     * <code>p_er</code>
     */
    private Literal getLiteralFor
	( recoder.service.ConstantEvaluator.EvaluationResult p_er ) {
	switch ( p_er.getTypeCode () ) {
	case recoder.service.ConstantEvaluator.BOOLEAN_TYPE:
	    return BooleanLiteral.getBooleanLiteral ( p_er.getBoolean () );
	case recoder.service.ConstantEvaluator.CHAR_TYPE:
	    return new CharLiteral    ( p_er.getChar    () );
	case recoder.service.ConstantEvaluator.DOUBLE_TYPE:
	    return new DoubleLiteral  ( p_er.getDouble  () );
	case recoder.service.ConstantEvaluator.FLOAT_TYPE:
	    return new FloatLiteral   ( p_er.getFloat   () );
	case recoder.service.ConstantEvaluator.BYTE_TYPE:
            return new IntLiteral     ( p_er.getByte() );
	case recoder.service.ConstantEvaluator.SHORT_TYPE:
            return new IntLiteral     ( p_er.getShort    () );
	case recoder.service.ConstantEvaluator.INT_TYPE:
	    return new IntLiteral     ( p_er.getInt     () );
	case recoder.service.ConstantEvaluator.LONG_TYPE:
	    return new LongLiteral    ( p_er.getLong    () );
	case recoder.service.ConstantEvaluator.STRING_TYPE:
	    if ( p_er.getString () == null )
	        return NullLiteral.NULL;
	    return new StringLiteral  ( p_er.getString  () );
	default:
	    Debug.out ( "Don't know how to handle type " +
			p_er.getTypeCode () + " of " + p_er );
	}
	return null;
    }

    /** 
     * convert a recoder TypeReference to a KeY TypeReference
     * (checks dimension and hands it over)
     */
    public TypeReference
	convert(recoder.java.reference.TypeReference tr) {

	recoder.abstraction.Type rType
	    = servConf.getSourceInfo().getType(tr);
	if (rType==null) return null; // because of 'void'

	KeYJavaType kjt = getKeYJavaType(rType);
	ExtList children = collectChildren(tr);
	TypeReference result = 
	    new TypeRef(children,
			kjt,
			tr.getDimensions());
	return result;
    }

    /** 
     * if an UncollatedReferenceQualifier appears throw a
     * ConvertExceception because these qualifiers have to be resolved
     * by running the CrossReferencer
     */
    public ProgramElement 
	convert(recoder.java.reference.UncollatedReferenceQualifier urq) {    
	recoder.java.ProgramElement pe = servConf.getCrossReferenceSourceInfo().resolveURQ(urq);
	if (pe != null && !(pe instanceof recoder.java.reference.UncollatedReferenceQualifier)) {
	    return (ProgramElement) callConvert(pe);
	}
	throw new PosConvertException("recoder2key: Qualifier "+urq.getName()+
				   " not resolvable.",
				      urq.getFirstElement().getStartPosition().getLine(),
				      urq.getFirstElement().getStartPosition().getColumn()-1);
    }


    protected recoder.java.declaration.VariableSpecification 
	getRecoderVarSpec(recoder.java.reference.VariableReference vr) {
	return servConf.getSourceInfo().
	    getVariableSpecification(servConf.getSourceInfo().getVariable(vr));
    }

    /**
     * converts a recoder variable reference. A ProgramVariable is created
     * replacing the variable reference.
     * @param vr the recoder variable reference.
     */
     public ProgramVariable convert
	 (recoder.java.reference.VariableReference vr) {

	 final recoder.java.declaration.VariableSpecification 
	     recoderVarspec = getRecoderVarSpec(vr);	 

	 if (!rec2key.mapped(recoderVarspec)) {
	     insertToMap(recoderVarspec, 
			 convert(recoderVarspec));
	 }

	 return (ProgramVariable)
	     ((VariableSpecification)rec2key.
	      toKeY(recoderVarspec)).getProgramVariable();
     }


     public BinaryAnd convert(recoder.java.expression.operator.BinaryAnd b) {
         return new BinaryAnd(collectChildren(b));
     }
     
     public BinaryOr convert(recoder.java.expression.operator.BinaryOr b) {
         return new BinaryOr(collectChildren(b));
     }
     
     public BinaryXOr convert(recoder.java.expression.operator.BinaryXOr b) {
         return new BinaryXOr(collectChildren(b));
     }
     
     public BinaryNot convert(recoder.java.expression.operator.BinaryNot b) {
         return new BinaryNot(collectChildren(b));
     }
     
     public BinaryAndAssignment convert(recoder.java.expression.operator.BinaryAndAssignment b) {
         return new BinaryAndAssignment(collectChildren(b));
     }
     
     public BinaryOrAssignment convert(recoder.java.expression.operator.BinaryOrAssignment b) {
         return new BinaryOrAssignment(collectChildren(b));
     }

     public BinaryXOrAssignment convert(recoder.java.expression.operator.BinaryXOrAssignment b) {
         return new BinaryXOrAssignment(collectChildren(b));
     }
     
    
     public ShiftLeft convert(recoder.java.expression.operator.ShiftLeft b) {
         return new ShiftLeft(collectChildren(b));
     }
     
     public ShiftRight convert(recoder.java.expression.operator.ShiftRight b) {
         return new ShiftRight(collectChildren(b));
     }
     
     public UnsignedShiftRight convert(recoder.java.expression.operator.UnsignedShiftRight b) {
         return new UnsignedShiftRight(collectChildren(b));
     }
     
     public ShiftLeftAssignment convert(recoder.java.expression.operator.ShiftLeftAssignment b) {
         return new ShiftLeftAssignment(collectChildren(b));
     }
     
     public ShiftRightAssignment convert(recoder.java.expression.operator.ShiftRightAssignment b) {
         return new ShiftRightAssignment(collectChildren(b));
     }
     
     public UnsignedShiftRightAssignment convert(recoder.java.expression.operator.UnsignedShiftRightAssignment b) {
         return new UnsignedShiftRightAssignment(collectChildren(b));
     }
    
   
     public Negative convert(recoder.java.expression.operator.Negative b) {
         return new Negative(collectChildren(b));
     }
     
     public Positive convert(recoder.java.expression.operator.Positive b) {
         return new Positive(collectChildren(b));
     }
     
     public Modulo convert(recoder.java.expression.operator.Modulo b) {
         return new Modulo(collectChildren(b));
     }
    
     public ModuloAssignment convert(recoder.java.expression.operator.ModuloAssignment b) {
         return new ModuloAssignment(collectChildren(b));
     }
    
     public Conditional convert(recoder.java.expression.operator.Conditional b) {
         return new Conditional(collectChildren(b));
     }
    
     
    /**
     * converts a recoder array length reference to a usual KeY field
     * reference
     */
    public FieldReference convert
	(recoder.java.reference.ArrayLengthReference alr) {
	recoder.abstraction.Type recoderType = servConf.
	    getCrossReferenceSourceInfo().getType(alr.getReferencePrefix());
	ArrayDeclaration ad = 
	    (ArrayDeclaration)getKeYJavaType(recoderType).getJavaType();

	final ProgramVariable length  = 
	    find("length", filterField(ad.length()));
	// the invocation of callConvert should work well as each array
	// length reference must have a reference prefix (at least this
	// is what i think)
	return new FieldReference
	    (length, (ReferencePrefix)callConvert(alr.getReferencePrefix()));
    }

    /**
     * converts a recoder package reference to the KeY package reference
     * @param pr the recoder package reference reference.
     */
     public PackageReference convert(recoder.java.reference.PackageReference pr) {
	 return new PackageReference(collectChildren(pr));
     }

    /**
     * converts a recoder field reference. A ProgramVariable is created
     * replacing the field reference.
     * @param fr the recoder field reference.
     */
     public Expression convert(recoder.java.reference.FieldReference fr) {
	 ProgramVariable pv;

	 recoder.java.declaration.FieldSpecification recoderVarSpec
	     = (recoder.java.declaration.FieldSpecification) getRecoderVarSpec(fr);

	 ReferencePrefix prefix = null;	

	 if (fr.getReferencePrefix() != null) {
	     prefix = (ReferencePrefix)callConvert(fr.getReferencePrefix());
	 }

	 if (recoderVarSpec == null) { 
	     // null means only bytecode available for this 
	     // field %%%
	     recoder.abstraction.Field recField = 
		 servConf.getSourceInfo().getField(fr);
	     recoder.abstraction.Type recoderType = 
		 servConf.getByteCodeInfo().getType(recField);	    
	     recoder.java.declaration.FieldSpecification fs 
		 = new recoder.java.declaration.FieldSpecification
		 (fr.getIdentifier());
	     pv = new LocationVariable
		 (new ProgramElementName(fs.getName(), 
		         recField.getContainingClassType().getFullName()),
		  getKeYJavaType(recoderType),
		  getKeYJavaType(recField.getContainingClassType()),
		  recField.isStatic());
	     insertToMap(fs, new FieldSpecification(pv));	     	     
	     return new FieldReference(pv, prefix);
	 } 

	 pv = getProgramVariableForFieldSpecification ( recoderVarSpec );
	 	 

	 if (!pv.isMember()) {	 
	     // in case of a cut, induction rule or s.th. else recoder will resolve 
	     // all variables of the created context as field references but
	     // in fact they are references to local variables, so we have
	     // to fix it here
	     // same applies for variables declared in program variables
	     // section
             return pv;
	 } 

	 return new FieldReference(pv, prefix);
     }
 

     /**
     * converts a recoder method reference. A
     * de.uka.ilkd.key.logic.op.ProgramMethod is created 
     * replacing the method reference.
     * @param mr the recoder method reference.
     * @return the Method the KeY Dependance
     */
     public MethodReference convert(recoder.java.reference.MethodReference mr) {
	 recoder.service.SourceInfo sourceInfo = servConf.getSourceInfo();
	 recoder.abstraction.Method method = sourceInfo.getMethod(mr);
         
         final ProgramMethod pm; 
	 if (!rec2key.mapped(method)) {
	     if (method instanceof recoder.java.declaration.MethodDeclaration) {
		 // method reference before method decl, also recursive calls.
		 //	do not use: 
		 final String oldCurrent = currentClass;
		 final String className = ((recoder.java.declaration.MethodDeclaration)
					   method).getMemberParent().getFullName();
		 recoder.io.DataLocation loc = servConf.getSourceFileRepository().
		     findSourceFile(className); 
		 if (loc instanceof recoder.io.DataFileLocation) {
		     currentClass = ((recoder.io.DataFileLocation)loc).getFile().getAbsolutePath();
		 } else {                     
		     currentClass = (loc == null ? null : ""+loc);
		 }		
		 pm = convert((recoder.java.declaration.MethodDeclaration)method);
		 // because of cycles when reading recursive programs		     
		 currentClass = oldCurrent;		 
	     } else {
	         // bytecode currently we do nothing
                 pm = null;                
             }
	 } else {
	     pm = (ProgramMethod)rec2key.toKeY(method);
         }

	 ExtList children = collectChildren(mr);
	 // convert reference prefix separately
	 ReferencePrefix prefix=null;
	 int prefixPos=mr.getIndexOfChild(mr.getReferencePrefix());
	 if (prefixPos!=-1) {
	     prefix=(ReferencePrefix)children.get(prefixPos);
	     children.remove(prefixPos);
	 }
	 
	 return new MethodReference 
	     (children, pm == null? new ProgramElementName(mr.getName()) : 
	      pm.getProgramElementName(), prefix, positionInfo(mr));
     }



    //--------------Special treatment because of ambiguities ----------


    public LabeledStatement convert
	(recoder.java.statement.LabeledStatement l) {

	ExtList children=collectChildren(l);
	Label lab=null;
	int labPos = l.getIndexOfChild(l.getIdentifier());	
	if (labPos!=-1) {
	    lab=(Label)children.get(labPos);
	    children.remove(labPos);
	}
	return new LabeledStatement(children, lab, positionInfo(l));
    }

    /**
     * converts a For.
     * @param f the For of recoder
     * @return the For of KeY
     */
    public For convert(recoder.java.statement.For f) {
	return new For(convertLoopInitializers(f), 
		       convertGuard(f), 
		       convertUpdates(f), 
		       convertBody(f),
		       collectComments(f),positionInfo(f));
    }

    /**
     * converts a While.
     * @param w the While of recoder
     * @return the While of KeY
     */
    public While convert(recoder.java.statement.While w) {
	return new While(convertGuard(w).getExpression(), 
			 convertBody(w), positionInfo(w), collectComments(w));
    }

    /**
     * converts a Do.
     * @param d the Do of recoder
     * @return the Do of KeY
     */
    public Do convert(recoder.java.statement.Do d) {
	return new Do(convertGuard(d).getExpression(), 
		      convertBody(d), collectComments(d), positionInfo(d));
    }

    /**
     * helper for convert(x) with x a LoopStatement. Converts the body of x.
     */
    protected Statement convertBody(recoder.java.statement.LoopStatement ls) {
	Object body = null;	
	if (ls.getBody() != null) {
	     body = callConvert(ls.getBody());
	}
	return (Statement) body;
    }

    /**
     * helper for convert(x) with x a LoopStatement. Converts the guard of x.
     */
    protected Guard convertGuard(recoder.java.statement.LoopStatement ls) {
	Object guard=null;
	if (ls.getGuard()!=null) {
	    guard = callConvert(ls.getGuard());
	}
	return new Guard((Expression)guard);
    }

    /**
     * helper for convert(x) with x a LoopStatement. Converts the updates of x.
     */
    protected ForUpdates
	convertUpdates(recoder.java.statement.LoopStatement ls) {
	    final ExtList updates = new ExtList();
	    final ExpressionMutableList recLoopUpdates = ls.getUpdates();
	     inLoopInit = true;
            if (recLoopUpdates!=null) {
		for (int i=0, sz=recLoopUpdates.size(); i<sz; i++) {
		    updates.add
			(callConvert(recLoopUpdates.getExpression(i)));
		}	 
    inLoopInit = false;
    return new ForUpdates(updates, positionInfo(ls));
	    }	    
            return null;
	}

    /**
     * helper for convert(x) with x a LoopStatement. Converts the loop
     * initializers of x. 
     */
    protected LoopInit
	convertLoopInitializers(recoder.java.statement.LoopStatement ls) {	    
        
        final LoopInit loopInit;
        
        final LoopInitializerMutableList initializers = 
            ls.getInitializers();
        if (initializers!=null) {
            final LoopInitializer[] result = 
                new LoopInitializer[initializers.size()];            
            for (int i=0, sz = initializers.size(); i<sz; i++) {
		inLoopInit = true;
                result[i] = (LoopInitializer) callConvert(initializers.
                        getLoopInitializer(i));	            
		inLoopInit = false;
            }
            loopInit = new LoopInit(result);
        } else {
            loopInit = null;
        }
        return loopInit;	 	 	    
    }

 

    /**
     * converts an ArrayReference. Special handling because the initializing
     * Expressions and the ReferencePrefix accessPath might not be disjunct.
     */
    public ArrayReference convert(recoder.java.reference.ArrayReference ar) {
	ExtList children=collectChildren(ar);
	ReferencePrefix prefix=null;

	int prefixPos=ar.getIndexOfChild(ar.getReferencePrefix());
	if (prefixPos!=-1) {
	    prefix=(ReferencePrefix)children.get(prefixPos);
	    children.remove(prefixPos);
	}
	return new ArrayReference(children, prefix);
    }

    /**
     * convert Breaks
     */
    public Break convert(recoder.java.statement.Break b) {
        return new Break(collectChildren(b));
    }

    /** convert Assert */
    public Assert convert(recoder.java.statement.Assert a) {        
        final Expression message;
        if (a.getMessage() != null) {
            message = (Expression)callConvert(a.getMessage());
        } else {
            message = null;
        }       
        return new Assert((Expression)callConvert(a.getCondition()), 
                message, positionInfo(a)); 
    }
    
    /**
     * converts a Case. 
     * Special handling because the initializing
     * Expression and Statements might not be disjunct.
     */
    public Case convert(recoder.java.statement.Case c) {
	ExtList children=collectChildren(c);
	Expression expr=null;
	int exprPos=c.getIndexOfChild(c.getExpression());	
	if (exprPos!=-1) {
	    expr=(Expression)children.get(exprPos);
	    children.remove(exprPos);
	}
	return new Case(children, expr, positionInfo(c));
    }

    /**
     * converts a New. 
     * Special handling because the ReferencePrefix and the TypeReference
     *  might not be disjunct.
     */
    public New convert(recoder.java.expression.operator.New n) {

	final recoder.list.ExpressionMutableList args = n.getArguments();		
	final recoder.java.reference.ReferencePrefix rp = n.getReferencePrefix();
	final recoder.java.reference.TypeReference tr = n.getTypeReference();
	
	Expression[] arguments = new Expression[args != null ? args.size() : 0];
	for (int i = 0; i<arguments.length; i++) {
	    arguments[i] = (Expression)callConvert(args.getExpression(i));
	}
	if (rp == null) {
	    return new New(arguments , 
			   (TypeReference) callConvert(tr), 
			   (ReferencePrefix)null);
	} else {
	    return new New(arguments , 
			   (TypeReference) callConvert(tr), 
			   (ReferencePrefix)callConvert(rp));
	}
    }

    //-----------------------------------------------------------


    public Import convert(recoder.java.Import im) {
	return new Import(collectChildren(im), 
			  im.isMultiImport());
    }

    private recoder.java.declaration.ClassDeclaration interactClassDecl() {
	recoder.java.declaration.ClassDeclaration classContext = 
 	    new recoder.java.declaration.ClassDeclaration
  		(null, 
		 new ImplicitIdentifier("<virtual_class_for_parsing" + interactCounter +">"), 
		 null, null, null);
	interactCounter++;	
 	classContext.setProgramModelInfo(servConf.getCrossReferenceSourceInfo());
	return classContext;
    }

    /** creates an empty RECODER compilation unit 
     * @return the recoder.java.CompilationUnit 
     */
    public Context createEmptyContext() {
 	recoder.java.declaration.ClassDeclaration classContext 
	    = interactClassDecl();
 	return new Context(servConf, classContext);
    }

    private VariableSpecification lookupVarSpec(ProgramVariable pv) {
	Iterator it=rec2key.elemsKeY().iterator();
	while (it.hasNext()) {
	    Object o=it.next();
	    if ((o instanceof VariableSpecification) 
		&& ((VariableSpecification)o).getProgramVariable()==pv){
		
		return (VariableSpecification)o;
	    }
	}
	return null;
    }

    private recoder.java.reference.TypeReference 
	name2typeReference(String typeName) {

	recoder.java.reference.PackageReference pr = null;
	String baseType = TypeNameTranslator.getBaseType(typeName);
	int idx = baseType.indexOf('.');
	int lastIndex = 0;
	while (idx != -1) {	    
	    pr = new recoder.java.reference.PackageReference
		(pr, new recoder.java.Identifier(baseType.substring(lastIndex, idx)));	    
	    lastIndex = idx + 1;
	    idx = baseType.indexOf('.', lastIndex);
	}

	recoder.java.Identifier typeId;
	if (baseType.charAt(0) == '<') {
	    typeId = new ImplicitIdentifier(baseType.substring(lastIndex));
	} else {	
	    typeId = new recoder.java.Identifier(baseType.substring(lastIndex));
	}
	recoder.java.reference.TypeReference result = 
	    new recoder.java.reference.TypeReference(pr, typeId);
	result.setDimensions(TypeNameTranslator.getDimensions(typeName));
	return result;
    }

    public void addProgramVariablesToClassContext
	(recoder.java.declaration.ClassDeclaration classContext,
	 ListOfProgramVariable vars, recoder.service.CrossReferenceSourceInfo csi) {

	HashMap names2var = new HashMap();	
	IteratorOfProgramVariable it = vars.iterator();
	java.util.HashSet names = new java.util.HashSet();
	recoder.list.MemberDeclarationMutableList list = classContext.getMembers();
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
		    throw new IllegalArgumentException("Variable "+var+" has no type");
		}

		String typeName = "";
		Type javaType = var.getKeYJavaType().getJavaType();
		typeName = javaType.getFullName();
		
		recoder.java.declaration.FieldDeclaration recVar = 
		    new recoder.java.declaration.FieldDeclaration
		    (null, name2typeReference(typeName),
		     new ExtendedIdentifier(keyVarSpec.getName()),
		     null);

		list.add(recVar);
		classContext.makeAllParentRolesValid();
		recoder.java.declaration.VariableSpecification rvarspec
		    = recVar.getVariables().getVariableSpecification(0);
		names2var.put(var.name().toString(), rvarspec);

		rvarspec.setProgramModelInfo(csi);
		insertToMap(recVar.getVariables()
			    .getVariableSpecification(0), keyVarSpec);
	    }

	((KeYCrossReferenceSourceInfo) csi).setNames2Vars(names2var);
	servConf.getChangeHistory().updateModel();
    }

    public Context createContext(ListOfProgramVariable pvs) {
	return createContext(pvs, servConf.getCrossReferenceSourceInfo());
    }

    public Context createContext(ListOfProgramVariable vars, 
				 recoder.service.CrossReferenceSourceInfo csi) {	
 	recoder.java.declaration.ClassDeclaration classContext = interactClassDecl();
	addProgramVariablesToClassContext(classContext, vars, csi);	
	return new Context(servConf, classContext);
    }
    
    // invoke model transformers
    protected void transformModel(recoder.list.CompilationUnitMutableList cUnits) {
        RecoderModelTransformer[] transformer =

        new RecoderModelTransformer[] {
                new JMLTransformer(servConf, cUnits, parsingLibs),
                new ImplicitFieldAdder(servConf, cUnits),
                new InstanceAllocationMethodBuilder(servConf, cUnits),
                new ConstructorNormalformBuilder(servConf, cUnits),
                new ClassPreparationMethodBuilder(servConf, cUnits),
                new ClassInitializeMethodBuilder(servConf, cUnits),
                new PrepareObjectBuilder(servConf, cUnits),
                new CreateBuilder(servConf, cUnits),
                new CreateObjectBuilder(servConf, cUnits),
                new JVMIsTransientMethodBuilder(servConf, cUnits)
                };

        final ChangeHistory cHistory = servConf.getChangeHistory();
        for (int i = 0; i < transformer.length; i++) {
            if (logger.isDebugEnabled()) {
                logger.debug("current transformer : "
                        + transformer[i].toString());
            }
	    transformer[i].execute();	    
	}
        if (cHistory.needsUpdate()) {
            cHistory.updateModel();    
        }
    }

    /**
     * retrieves a field with the given name out of the list
     * @param name a String with the name of the field to be looked for
     * @param fields the ListOfField where we have to look for the field
     * @return the program variable of the given name or null if not
     * found
     */
    protected ProgramVariable find(String name, ListOfField fields) {
	IteratorOfField it = fields.iterator();
	while (it.hasNext()) {
	    Field field = it.next();
	    if (name.equals(field.getName())) {
		return (ProgramVariable)
		    ((FieldSpecification)field).getProgramVariable();
	    }
	}
	return null;
    }

    /**
     * extracts all field specifications out of the given
     * list. Therefore it descends into field declarations.
     * @param list the ExtList with the members of a type declaration
     * @return a ListOfField the includes all field specifications found
     * int the field declaration of the given list
     */
    private ListOfField filterField(ExtList list) {
	ListOfField result = SLListOfField.EMPTY_LIST;
	Iterator it = list.iterator();
	while (it.hasNext()) {
	    Object pe = it.next();
	    if (pe instanceof FieldDeclaration) {
		result = result.prepend
		    (filterField((FieldDeclaration)pe));
	    }
	}
	return result;
    }

    /**
     * extracts all fields out of fielddeclaration
     * @param field the FieldDeclaration of which the field
     * specifications have to be extracted
     * @return a ListOfField the includes all field specifications found
     * int the field declaration of the given list
     */
    protected ListOfField filterField(FieldDeclaration field) {
	ListOfField result = SLListOfField.EMPTY_LIST;
	ArrayOfFieldSpecification spec = field.getFieldSpecifications();
	for (int i = spec.size()-1; i>=0; i--) {
	    result = result.prepend(spec.getFieldSpecification(i));
	} 
	return result;
    }


    // array type creation


    /**
     * creates an implicit field of the given name and type
     * @param name a String with the name of the implicit field
     * @param typeRef a TypeReference refering to the type as which the
     * new field has to be declared
     * @param isStatic a boolean that forces a field to become static or
     *  non static 
     * @return the new created FieldDeclaration <br></br>
     *     </code>private (static) typeRef name</code>
     */
    private FieldDeclaration createImplicitArrayField
	(String name, TypeReference typeRef, boolean isStatic, 
	 KeYJavaType prefix) {

	ImplicitFieldSpecification varSpec = 
	    new ImplicitFieldSpecification
	    (new LocationVariable(new ProgramElementName(name, 
	            prefix.getSort().name().toString()),
	            typeRef.getKeYJavaType(), prefix, 
	            isStatic), 
	     typeRef.getKeYJavaType());	
	// no recoder dependance
	// insertToMap(recoderVarSpec, varSpec);
	Modifier[] modifiers = new Modifier[isStatic ? 2 : 1];
	modifiers[0] = new Private();
	if (isStatic) {
	    modifiers[1] = new Static();
	}
	return new FieldDeclaration
	    (modifiers, typeRef, new FieldSpecification[]{varSpec},
	     false);
    }



    /**
     * Adds several implicit fields and methods to given list of members.
     * @param members an ExtList with the members of parent
     * @param parent the KeYJavaType of the array to be enriched by its
     * implicit members
     * @param baseType the KeYJavaType of the parent's element type
     */
    private void addImplicitArrayMembers(ExtList members, 
					 KeYJavaType parent, 
					 KeYJavaType baseType,
					 ProgramVariable len) {
	
	final Type base = baseType.getJavaType();
	final int dimension = base instanceof ArrayType ? 
	    ((ArrayType)base).getDimension() + 1 : 1;
	TypeRef parentReference = new TypeRef(new ProgramElementName
					      (""+parent.getSort().name()), 
					      dimension, null, parent); 
        KeYJavaType integerType = 
            getKeYJavaType(servConf.getNameInfo().getIntType());
	
        members.add(createImplicitArrayField
		    (ImplicitFieldAdder.IMPLICIT_NEXT_TO_CREATE, 
		     new TypeRef(integerType), true, parent));
	
	final recoder.service.NameInfo nameInfo = servConf.getNameInfo();
	

	TypeReference booleanArrayTypeRef;
	if (base == PrimitiveType.JAVA_BOOLEAN && dimension == 1) {
	    booleanArrayTypeRef = parentReference;
	} else {
	    booleanArrayTypeRef = new TypeRef
		(getKeYJavaType(nameInfo.getArrayType(nameInfo.getBooleanType())),1);
	}
	members.add(createImplicitArrayField
			(ImplicitFieldAdder.IMPLICT_ARRAY_TRA_INITIALIZED, 
			 booleanArrayTypeRef, false, parent));    
	
	// add methods
	// the only situation where base can be null is in case of a
	// reference type
	Expression defaultValue = (base != null ? 
				   base.getDefaultValue() : 
				   NullLiteral.NULL);

	ListOfField fields = filterField(members);

	ProgramVariable length = len;//find("length", fields);

	if (arrayMethodBuilder == null) {
	    initArrayMethodBuilder();
	}
	final ProgramMethod prepare = arrayMethodBuilder.
	    getPrepareArrayMethod(parentReference, length, defaultValue, fields);
        
        members.add(arrayMethodBuilder.
                    getArrayInstanceAllocatorMethod(parentReference));
	members.add(prepare);
	members.add(arrayMethodBuilder.
		    getCreateArrayHelperMethod(parentReference, length, fields));
	members.add(arrayMethodBuilder.
		    getCreateArrayMethod(parentReference, prepare, fields));
	members.add(transientArrayMethodBuilder.
		    getCreateTransientArrayHelperMethod(parentReference, 
							length, 
							fields));
	members.add(transientArrayMethodBuilder.
		    getCreateTransientArrayMethod(parentReference, 
						  length, 
						  prepare, fields));
   }


    /**
     * creates the field declaration for the public final integer field
     * <code>length</code>
     */
    private FieldDeclaration createSuperArrayType() {
	KeYJavaType integerType = 
	    getKeYJavaType(servConf.getNameInfo().getIntType());

        final KeYJavaType superArrayType = new KeYJavaType();
        rec2key.setSuperArrayType(superArrayType);
	FieldSpecification specLength = new FieldSpecification
	    (new LocationVariable
		(new ProgramElementName("length"), integerType, 
                        superArrayType, false));       
	FieldDeclaration f = new FieldDeclaration
	    (new Modifier[]{new Public(), new Final()},
	     new TypeRef(integerType),
	     new FieldSpecification[]{specLength}, false);
        superArrayType.setJavaType(new SuperArrayDeclaration(f));
	return f;
    }

    public ArrayDeclaration createArrayType(KeYJavaType baseType, 
					    KeYJavaType arrayType) {
	ExtList members = new ExtList();
	if (rec2key().getSuperArrayType()==null) {
	    createSuperArrayType(); // we want to have exactly one
				    // length attribute for this R2K
				    // instance (resolving
				    // a.length=a.length might get
				    // impossible otherwise),
				    // therefore we introduce a 'super
				    // array class' which contains the
				    // length attribute
	}
	final FieldDeclaration length = ((SuperArrayDeclaration)
					 rec2key().getSuperArrayType().
                                             getJavaType()).length();
	final TypeReference baseTypeRef;

	if (baseType.getJavaType() != null) {
	    baseTypeRef = new TypeRef(baseType);
	} else {
	    baseTypeRef = new TypeRef
		(new ProgramElementName
		 (baseType.getSort().name().toString()), 0, null, baseType);
	}
	members.add(baseTypeRef);
	addImplicitArrayMembers(members, 
				arrayType, 
				baseType,
				(ProgramVariable)			       
				length.getFieldSpecifications().
				getFieldSpecification(0).getProgramVariable());

	return new ArrayDeclaration(members, baseTypeRef, rec2key().getSuperArrayType());
    }

}
