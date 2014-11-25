package de.uka.ilkd.key.testgen;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;
import de.uka.ilkd.key.gui.testgen.TGInfoDialog;
import de.uka.ilkd.key.gui.testgen.TestGenerationSettings;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.model.Heap;
import de.uka.ilkd.key.smt.model.Model;
import de.uka.ilkd.key.smt.model.ObjectVal;
import de.uka.ilkd.key.testgen.oracle.OracleGenerator;
import de.uka.ilkd.key.testgen.oracle.OracleMethod;
import de.uka.ilkd.key.testgen.oracle.OracleTermCall;

/**
 * @author gladisch
 * @author herda
 */
public class TestCaseGenerator {
	private static final String NULLABLE = "/*@ nullable */";
	public static final String ALL_OBJECTS = "allObjects";
	public static final String ALL_INTS = "allInts";
	public static final String ALL_BOOLS = "allBools";
	public static final String ALL_HEAPS = "allHeaps";
	public static final String ALL_FIELDS = "allFields";
	public static final String ALL_SEQ = "allSeq";
	public static final String ALL_LOCSETS = "allLocSets";
	
	public static final String OBJENESIS_NAME = "objenesis-2.1.jar";
	
	public static final String OLDMap = "old";
	
	public static final String TAB = "   ";
	private Services services;
	private Proof proof;
	static int fileCounter = 0;
	boolean junitFormat;
	private static final String DONT_COPY = "aux"; // Classes of the Java
	                                               // environment needed by KeY
	                                               // can be placed in this
	                                               // subdirectory.

	public static boolean modelIsOK(Model m) {
		return m != null && !m.isEmpty() && m.getHeaps() != null
		        && m.getHeaps().size() > 0 && m.getTypes() != null;
	}

	protected boolean useRFL;
	protected ReflectionClassCreator rflCreator;
	private final String dontCopy;
	protected final String modDir;
	protected final String directory;
	private TGInfoDialog logger;
	private String fileName;
	private String MUTName;
	private ProofInfo info;
	private OracleGenerator oracleGenerator;
	private List<OracleMethod> oracleMethods;
	private String oracleMethodCall;
	private final Map<Sort, StringBuffer> sortDummyClass;
	final String DummyPostfix = "DummyImpl";
	// TODO: in future remove this string and provide the file in the
	// KeY-project
	private String compileWithOpenJML = "#!/bin/bash\n\n"
	        + "if [ -e \"openjml.jar\" ]\n"
	        + "then\n"
	        + "   java -jar openjml.jar -cp \".\" -rac *.java\n"
	        + "else\n"
	        + "   echo \"openjml.jar not found!\"\n"
	        + "   echo \"Download openJML from http://sourceforge.net/projects/jmlspecs/files/\"\n"
	        + "   echo \"Copy openjml.jar into the directory with test files.\"\n"
	        + "fi\n";
	
	private String createCompileWithOpenJML(String openJMLPath, String objenesisPath){
		return "#!/bin/bash\n\n"
		        + "if [ -e \""+openJMLPath+File.separator+"openjml.jar\" ] \n"
		        + "then\n" 
		        + "   if [ -e \""+objenesisPath+File.separator+OBJENESIS_NAME+"\" ]\n"
		        + "   then\n"
		        + "      java -jar "+openJMLPath+File.separator+"openjml.jar -cp \"."+objenesisPath+File.separator+OBJENESIS_NAME+"\" -rac *.java\n"
		        + "   else\n"
		        + "      echo \"objenesis-2.1.jar not found!\"\n"
		        + "   fi\n"
		        + "else\n"
		        + "   echo \"openjml.jar not found!\"\n"
		        
		        + "   echo \"Download openJML from http://sourceforge.net/projects/jmlspecs/files/\"\n"
		        + "   echo \"Copy openjml.jar into the directory with test files.\"\n"
		        + "fi\n";
	}
	// TODO: in future remove this string and provide the file in the
	// KeY-project
	private String executeWithOpenJML;

	private String createExecuteWithOpenJML(String path, String objenesisPath){
		return "#!/bin/bash\n"
		        + "if [ -e \""+path+File.separator+"jmlruntime.jar\" ]\n"
		        + "then"
		        + "  if [ -e \""+path+File.separator+"jmlspecs.jar\" ]\n"
		        + "  then\n"
		        + "     if [ -e \""+objenesisPath+File.separator+OBJENESIS_NAME+"\" ]\n"
		        + "     then\n"
		        + "        if [ \"$1\" = \"\" ] ; then\n"
		        + "           echo \"Provide the test driver as an argument (without .java postfix). For example:\"\n"
		        + "           echo \"  executeWithOpenJML.sh TestGeneric0 \"\n"
		        + "           echo \"Make sure that jmlruntime.jar and jmlspecs.jar are in the\"\n"
		        + "           echo \"current directory.\"\n"
		        + "           quit\n"
		        + "        else\n"
		        + "           java -cp "+objenesisPath+File.separator+OBJENESIS_NAME+":"+path+File.separator+"jmlruntime.jar:"+path+File.separator+"jmlspecs.jar:. $1\n"
		        + "        fi\n"
		        + "      else\n"
		        + "         echo \"objenesis-2.1.jar not found!\"\n"
		        + "      fi\n"
		        + "else\n"
		        + "  echo \"jmlspecs.jar not found!\"\n"
		        + "  echo \"Download openJML from http://sourceforge.net/projects/jmlspecs/files/\"\n"
		        + "  echo \"Copy jmlspecs.jar into the directory with test files.\"\n"
		        + "  quit\n"
		        + "fi\n"
		        + "else\n"
		        + "   echo \"jmlruntime.jar not found!\"\n"
		        + "   echo \"Download openJML from http://sourceforge.net/projects/jmlspecs/files/\"\n"
		        + "   echo \"Copy jmlruntime.jar into the directory with test files.\"\n"
		        + "   quit\n" + "fi\n";
	}
	public TestCaseGenerator(Proof proof) {
		super();
		final TestGenerationSettings settings = ProofIndependentSettings.DEFAULT_INSTANCE
		        .getTestGenerationSettings();
		this.proof = proof;
		services = proof.getServices();
		junitFormat = settings.useJunit();
		useRFL = settings.useRFL();
		modDir = services.getJavaModel().getModelDir();
		dontCopy = modDir + File.separator + TestCaseGenerator.DONT_COPY;
		directory = settings.getOutputFolderPath();
		sortDummyClass = new HashMap<Sort, StringBuffer>();		
		info = new ProofInfo(proof);
		MUTName = info.getMUT().getFullName();	
		rflCreator = new ReflectionClassCreator();
		executeWithOpenJML = createExecuteWithOpenJML(settings.getOpenjmlPath(),settings.getObjenesisPath());
		compileWithOpenJML = createCompileWithOpenJML(settings.getOpenjmlPath(), settings.getObjenesisPath());
		oracleGenerator  =new OracleGenerator(services,rflCreator, useRFL);
		if(junitFormat){
			//System.out.println("Translating oracle");
			try{
				oracleMethods = new LinkedList<OracleMethod>();
				oracleMethodCall = getOracleAssertion(oracleMethods);
				
			}catch(Exception e){
				e.printStackTrace();
			}
		}
	}
	
	
	
	private Set<ObjectVal> getPrestateObjects(Model m){
		
		Set<ObjectVal> result  =new HashSet<ObjectVal>();
		
		Set<String> refs = oracleGenerator.getPrestateTerms();
		try{
			for(String ref : refs){
				result.addAll(m.getNecessaryPrestateObjects(ref));
			}
		}catch(Exception e){
			e.printStackTrace();
		}
		
		
		return result;
		
		
	}
	
	
	
	public String getMUTCall(){
		IProgramMethod m = info.getMUT();		
		String name = m.getFullName();
		String params = "";
		for(ParameterDeclaration p : m.getParameters()){
			for(VariableSpecification v : p.getVariables()){
				IProgramVariable var = v.getProgramVariable();
				params = params +"," +var.name();
			}
		}		
		if(params.length() > 0){
			params = params.substring(1);
		}
		
		String caller;
		if(m.isStatic()){
			caller = info.getTypeOfClassUnderTest().getName();
		}
		else{
			caller = "self";
		}
		
		if(m.getReturnType().equals(KeYJavaType.VOID_TYPE)){
			return caller+"."+name+"("+params+");";
		}
		else{
			String returnType = m.getReturnType().getFullName();
			return returnType +" result = "+caller+"."+name+"("+params+");";
		}		
	}

	protected String buildDummyClassForAbstractSort(Sort sort) {
		final JavaInfo jinfo = services.getJavaInfo();
		final KeYJavaType kjt = jinfo.getKeYJavaType(sort);
		final String className = getDummyClassNameFor(sort);
		if (sortDummyClass.containsKey(sort)) {
			return className;
		}
		final StringBuffer sb = new StringBuffer();
		sortDummyClass.put(sort, sb); // Put the string buffer as soon as
		                              // possible, due to possible recursive
		                              // calls of this method.
		sb.append("import " + sort.declarationString() + ";\n\n");
		sb.append("class " + className + " implements "
		        + sort.declarationString() + "{\n"); // TODO:extends or
		                                             // implements depending if
		                                             // it is a class or
		                                             // interface.
		sb.append(" public " + className + "(){ };\n"); // default constructor
		final Iterator<IProgramMethod> methods = jinfo
		        .getAllProgramMethods(kjt).iterator();
		while (methods.hasNext()) {
			final IProgramMethod m = methods.next();
			if (m.getFullName().indexOf('<') > -1) {
				continue;
			}
			if (m.isPrivate() || m.isFinal() || !m.isAbstract()) {
				continue;
			}
			sb.append(" ");
			final MethodDeclaration md = m.getMethodDeclaration();
			// sb.append(md.toString()+ "\n");
			if (m.isProtected()) {
				sb.append("protected ");
			}
			if (m.isPublic()) {
				sb.append("public ");
			}
			if (m.isFinal()) {
				sb.append("final "); // Is this possible?
			}
			if (m.isStatic()) {
				sb.append("static ");
			}
			if (m.isSynchronized()) {
				sb.append("synchronized ");
			}
			if (md.getTypeReference() == null) {
				sb.append("void ");
			} else {
				sb.append(md.getTypeReference().toString() + " ");
			}
			sb.append(m.getName() + "(");
			final Iterator<ParameterDeclaration> pdIter = md.getParameters()
			        .iterator();
			int varcount = 0;
			while (pdIter.hasNext()) {
				final ParameterDeclaration pd = pdIter.next();
				if (pd.isFinal()) {
					sb.append("final ");
				}
				if (pd.getTypeReference() == null) {
					sb.append("void /*unkown type*/ ");
				} else {
					sb.append(pd.getTypeReference().toString() + " ");
				}
				if (pd.getVariables().isEmpty()) {
					sb.append("var" + varcount);
				} else {
					sb.append(pd.getVariables().iterator().next().getFullName());
				}
				if (pdIter.hasNext()) {
					sb.append(", ");
				}
				varcount++;
			}
			sb.append(")");
			if (md.getThrown() != null) {
				sb.append(" throws " + md.getThrown().getTypeReferenceAt(0)
				        + " \n ");
			}
			if (md.getTypeReference() == null) {
				sb.append("{ };");
			} else {
				final String type = md.getTypeReference().toString();
				if (isNumericType(type)) {
					sb.append("{ return 0;}");
				} else if (type.equals("boolean")) {
					sb.append("{ return true;}");
				} else if (type.equals("char")) {
					sb.append("{ return 'a';}");
				} else {
					boolean returnNull = true;
					try {
						final String retType = md.getTypeReference()
						        .getKeYJavaType().getSort().name().toString();
						if (retType.equals("java.lang.String")) {
							sb.append("{ return \"" + className + "\";}");
							returnNull = false;
						}
					} catch (final Exception e) {
						returnNull = true;
					}
					if (returnNull) {
						sb.append("{ return null;}");
					}
				}
			}
			sb.append("\n");
		}
		sb.append("}");
		// System.out.println("--------------------\n"+sb.toString());
		return className;
	}

	private void copyFiles(final String srcName, final String targName)
	        throws IOException {
		// We don't want to copy the Folder with API Reference
		// Implementation
		if (srcName.equals(dontCopy)) {
			return;
		}
		// Create the File with given filename and check if it exists and if
		// it's readable
		final File srcFile = new File(srcName);
		if (!srcFile.exists()) {
			throw new IOException("FileCopy: " + "no such source file: "
			        + srcName);
		}
		if (!srcFile.canRead()) {
			throw new IOException("FileCopy: " + "source file is unreadable: "
			        + srcName);
		}
		if (srcFile.isDirectory()) {
			final String newTarget;
			if (srcName.equals(modDir)) {
				newTarget = targName;
			} else {
				newTarget = targName + File.separator + srcFile.getName();
			}
			for (final String subName : srcFile.list()) {
				copyFiles(srcName + File.separator + subName, newTarget);
			}
		} else if (srcFile.isFile()) {
			final File targDir = new File(targName);
			if (!targDir.exists()) {
				targDir.mkdirs();
			}
			final File targFile = new File(targDir, srcFile.getName());
			if (targFile.exists()) {
				if (!targFile.canWrite()) {
					throw new IOException("FileCopy: "
					        + "destination file is unwriteable: " + targName);
				}
			}
			FileInputStream src = null;
			FileOutputStream targ = null;
			try {
				src = new FileInputStream(srcFile);
				targ = new FileOutputStream(targFile);
				final byte[] buffer = new byte[4096];
				int bytesRead;
				while ((bytesRead = src.read(buffer)) != -1) {
					targ.write(buffer, 0, bytesRead); // write
				}
			} finally {
				if (src != null) {
					try {
						src.close();
					} catch (final IOException e) {
						;
					}
				}
				if (targ != null) {
					try {
						targ.close();
					} catch (final IOException e) {
						;
					}
				}
			}
		} else {
			throw new IOException("FileCopy: " + srcName
			        + " is neither a file nor a directory!");
		}
	}

	protected void createDummyClasses() {
		for (final Sort s : sortDummyClass.keySet()) {
			final StringBuffer sb = sortDummyClass.get(s);
			final String file = getDummyClassNameFor(s) + ".java";
			writeToFile(file, sb);
		}
	}
	
    /** Creates the RFL.java file, that provides setter and getter methods using the reflection API
     *  as well as object creation functions based on the objenesis library.
     */
	protected void createRFLFile(){
		writeToFile(ReflectionClassCreator.NAME_OF_CLASS + ".java", rflCreator.createClass());
	}

	protected void createOpenJMLShellScript() {
		StringBuffer sb = new StringBuffer();
		String filestr = "compileWithOpenJML.sh";
		File file = new File(directory + modDir + File.separator + filestr);
		if (!file.exists()) {
			sb.append(compileWithOpenJML);
			writeToFile(filestr, sb);
		}
		filestr = "executeWithOpenJML.sh";
		file = new File(directory + modDir + File.separator + filestr);
		if (!file.exists()) {
			sb = new StringBuffer();
			sb.append(executeWithOpenJML);
			writeToFile(filestr, sb);
		}
	}

	protected void exportCodeUnderTest() {
		try {
			// Copy the involved classes without modification
			copyFiles(modDir, directory + modDir);
		} catch (final IOException e) {
			e.printStackTrace();
		}
	}

	private boolean filterVal(String s) {
		if (s.startsWith("#a") || s.startsWith("#s") || s.startsWith("#h")
		        || s.startsWith("#l") || s.startsWith("#f")) {
			return false;
		} else {
			return true;
		}
	}

	public String generateJUnitTestCase(Model m) {
		fileName = "TestGeneric" + TestCaseGenerator.fileCounter;
		String mut = getMUTCall();
		if (mut == null) {
			mut = "<method under test> //Manually write a call to the method under test, because KeY could not determine it automatically.";
		} else {
			fileName += "_" + MUTName;
		}
		final StringBuffer testCase = new StringBuffer();
		testCase.append(getFilePrefix(fileName) + "\n");
		testCase.append(getMainMethod(fileName, 1) + "\n\n");
		testCase.append(getTestMethodSignature(0) + "{\n");
		testCase.append("   //Test preamble: creating objects and intializing test data"
		        + generateTestCase(m) + "\n\n");
		testCase.append("   //Calling the method under test\n   " + mut
		        + "\n");
		testCase.append("}\n}");
		logger.writeln("Writing test file to:" + directory + modDir
		        + File.separator + fileName);
		writeToFile(fileName + ".java", testCase);
		exportCodeUnderTest();
		createDummyClasses();
		try{
			if(useRFL)createRFLFile();
		}catch(Exception ex){
			logger.writeln("Error: The file RFL.java is either not generated or it has an error.");
		}
		createOpenJMLShellScript();
		TestCaseGenerator.fileCounter++;
		return testCase.toString();
	}
	
	
	
	protected String getOracleAssertion(List<OracleMethod> oracleMethods){		
		Term postcondition = getPostCondition();
		
		OracleMethod oracle = oracleGenerator.generateOracleMethod(postcondition);
		
		
		
		OracleTermCall oracleCall = new OracleTermCall(oracle, oracle.getArgs());
		
		oracleMethods.add(oracle);
		oracleMethods.addAll(oracleGenerator.getOracleMethods());
		
		System.out.println("Modifier Set: "+oracleGenerator.getOracleLocationSet(info.getAssignable()));
		
		
		return "assertTrue("+oracleCall.toString()+");";
	}

	private Term getPostCondition() {
		return info.getPostCondition();
	}
	public String generateJUnitTestSuite(Collection<SMTSolver> problemSolvers) {
		
		fileName = "TestGeneric" + TestCaseGenerator.fileCounter;
		String mut = getMUTCall(); 
		if (mut == null) {
			mut = "<method under test> //Manually write a call to the method under test, because KeY could not determine it automatically.";
		} else {
			fileName += "_" + MUTName;
		}
		final StringBuffer testSuite = new StringBuffer();
		testSuite.append(getFilePrefix(fileName) + "\n");
		final StringBuffer testMethods = new StringBuffer();
		int i = 0;
		for (final SMTSolver solver : problemSolvers) {
			try {
				final StringBuffer testMethod = new StringBuffer();
				final String originalNodeName = solver.getProblem().getGoal()
				        .proof().name().toString();
				boolean success = false;
				if (solver.getSocket().getQuery() != null) {
					final Model m = solver.getSocket().getQuery().getModel();
					if (TestCaseGenerator.modelIsOK(m)) {
						logger.writeln("Generate: " + originalNodeName);
						testMethod.append("  //" + originalNodeName + "\n");
						testMethod.append(getTestMethodSignature(i) + "{\n");
						testMethod
						        .append("   //Test preamble: creating objects and intializing test data"
						                + generateTestCase(m) + "\n\n");
						
						//info.getCode();
						if(junitFormat){
							testMethod.append(TAB+"//Other variables\n" + getOtherVariables(m)+"\n");
						}
						testMethod
						        .append("   //Calling the method under test\n   "
						                + info.getCode() + "\n");
						
						
						if(junitFormat){
							testMethod.append("   //calling the test oracle\n"+TAB+oracleMethodCall+"\n");
						}
						
						testMethod.append(" }\n\n");
						i++;
						success = true;
						testMethods.append(testMethod);
					}
				}
				if (!success) {
					logger.writeln("A model (test data) was not generated for:"
					        + originalNodeName);
				}
			} catch (final Exception ex) {
				for(StackTraceElement ste: ex.getStackTrace()){
					logger.writeln(ste.toString());
				}
				logger.writeln("A test case was not generated due to an exception. Continuing test generation...");
			}
		}
		if (i == 0) {
			logger.writeln("Warning: no test case was generated. Adjust the SMT solver settings (e.g. timeout) in Options->SMT Solvers.");
		} else if (i < problemSolvers.size()) {
			logger.writeln("Warning: SMT solver could not solve all test data constraints. Adjust the SMT solver settings (e.g. timeout) in Options->SMT Solvers.");
		}
		testSuite.append(getMainMethod(fileName, i) + "\n\n");
		testSuite.append(testMethods);
		
		if(junitFormat){
			for(OracleMethod m : oracleMethods){
				testSuite.append("\n\n");
				testSuite.append(m);
			}
		}
		
		
		testSuite.append("\n}");
		writeToFile(fileName + ".java", testSuite);
		logger.writeln("Writing test file to:" + directory + modDir
		        + File.separator + fileName + ".java");
		exportCodeUnderTest();
		createDummyClasses();
		try{
			if(useRFL)createRFLFile();
		}catch(Exception ex){
			logger.writeln("Error: The file RFL.java is either not generated or it has an error.");
		}
		createOpenJMLShellScript();
		TestCaseGenerator.fileCounter++;
		return testSuite.toString();
	}
	
	private String getOtherVariables(Model m) {
		String result = "";
		
		
		
		for(Term c : oracleGenerator.getConstants()){
			if(!m.getConstants().containsKey(c.toString())){
				String init = "null";
				if(c.sort().equals(services.getTypeConverter().getIntegerLDT().targetSort())){
					init = "0";
				}
				else if(c.sort().equals(services.getTypeConverter().getBooleanLDT().targetSort())){
					init = "false";
				}
				
				result += "\n"+TAB+ c.sort().name() + " " + c + " = " + init + ";";
				result += "\n"+TAB+ c.sort().name() + " " + getPreName(c.toString()) + " = " + init + ";";
				
			}
		}
		return result;
	}
	private boolean isInPrestate(Collection<? extends ObjectVal> prestate, ObjectVal o){
		return true;
	}
	
	private boolean isInPrestate(Collection<? extends ObjectVal> prestate, String name){
		
		
		
		return true;
// TODO return only needed objects		
//		for(ObjectVal o : prestate){
//			String oName = createObjectName(o);
//			if(oName.equals(name)){
//				return true;
//			}
//		}
//		
//		return false;
	}
	
	public String generateModifierSetAssertions(Model m){
		StringBuffer res  =new StringBuffer();
		
		res.append(TAB + "//Modifier set assertions");
		
		
		
		return res.toString();
	}

	public String generateTestCase(Model m) {
/*		if(useRFL){
			for(Sort s:m.getTypes().getJavaSorts()){
				System.out.println("Adding sort:"+s.name());
				rflCreator.addSort(s);
			}
		}
*/
		m.removeUnnecessaryObjects();
		
		Set<String> objects = new HashSet<String>();
		
		final List<Assignment> assignments = new LinkedList<Assignment>();
		Heap heap = null;
		for (final Heap h : m.getHeaps()) {
			if (h.getName().equals("heap")) {
				heap = h;
				break;
			}
		}
		
		//Set<ObjectVal> prestate = getPrestateObjects(m);
		Set<ObjectVal> prestate = new HashSet<ObjectVal>();
		if (heap != null) {
			
			
			// create objects
			for (final ObjectVal o : heap.getObjects()) {
				if (o.getName().equals("#o0")) {
					continue;
				}
				final String type = getSafeType(o.getSort());
				String right;
				if (type.endsWith("[]")) {
					right = "new " + type.substring(0, type.length() - 2) + "["
					        + o.getLength() + "]";
				} else {
					if(useRFL){
						right = "RFL.new"+ReflectionClassCreator.cleanTypeName(type)+"()";
						Sort oSort = o.getSort();
						rflCreator.addSort(type);
						//rflCreator.addSort(oSort!=null?oSort.name().toString():"Object");
						//System.out.println("Adding sort (create Object):"+ (oSort!=null?oSort.name().toString():"Object"));
					}else
						right = "new " + type + "()";
				}
				
				String objName = createObjectName(o);
				objects.add(objName);
				assignments.add(new Assignment(type, objName, right));
				if(junitFormat && isInPrestate(prestate, o)){
					assignments.add(new Assignment(type, getPreName(objName), right));
				}
			}
		}
		// init constants
		for (final String c : m.getConstants().keySet()) {
			String val = m.getConstants().get(c);
			if (filterVal(val) && !c.equals("null")) {
				String type = "int";
				if (val.equals("true") || val.equals("false")) {
					type = "boolean";
				} else if (val.startsWith("#o")) {
					final ObjectVal o = getObject(heap, val);
					if (o != null) {
						if (val.equals("#o0")
						        && m.getTypes().getOriginalConstantType(c) != null) {
							type = m.getTypes().getOriginalConstantType(c)
							        .name().toString();
						} else {
							type = o.getSort().name().toString();
						}
					} else {
						type = "Object";
					}
					type = NULLABLE +" "+ type;
				}
				val = translateValueExpression(val);
				assignments.add(new Assignment(type, c, val));
				if(junitFormat && type.startsWith(NULLABLE) && isInPrestate(prestate, val)){
					assignments.add(new Assignment(type, getPreName(c), getPreName(val)));
				}
			}
		}
		// init fields
		if (heap != null) {
			for (final ObjectVal o : heap.getObjects()) {
				if (o.getName().equals("#o0")) {
					continue;
				}
				final String receiverObject = createObjectName(o);
				for (final String f : o.getFieldvalues().keySet()) {
					if (f.contains("<") || f.contains(">")) {
						continue;
					}
					String fieldName = f.substring(f.lastIndexOf(":") + 1);
					fieldName = fieldName.replace("|", "");
					String val = o.getFieldvalues().get(f);
					final String vType = getTypeOfValue(heap, m, val);
					rflCreator.addSort(vType); //possible bug if vType represents an abstract type or an interface. See: getSafeType.
					//System.out.println("Added sort (init fields):"+vType);
					val = translateValueExpression(val);
					final String rcObjType = getSafeType(o.getSort());
					assignments
					        .add(new Assignment(new RefEx(rcObjType,receiverObject,vType,fieldName), val));
					
					if(junitFormat && isInPrestate(prestate, o)){
						//if value that is pointed to is object and in prestate then use prestate object
						if(!vType.equals("int") && !vType.equals("boolean") && isInPrestate(prestate, val)){
							val = getPreName(val);
						}					
						assignments
				        .add(new Assignment(new RefEx(rcObjType,getPreName(receiverObject),vType,fieldName), val));
					}
					
				}
				if (o.getSort() != null
				        && o.getSort().name().toString().endsWith("[]")) {
					
					String safeType = getSafeType(o.getSort());
					rflCreator.addSort(safeType);
					//System.out.println("Added sort (init array fields):"+safeType);					

					for (int i = 0; i < o.getLength(); i++) {
						final String fieldName = "[" + i + "]";
						String val = o.getArrayValue(i);
						val = translateValueExpression(val);
						assignments.add(new Assignment(receiverObject + fieldName, val));
						//assignments.add(new Assignment("",new RefArrayEx("","",name,""+i), val));
						
						if(junitFormat && isInPrestate(prestate, o)){
							assignments.add(new Assignment(getPreName(receiverObject) + fieldName, val));
						}
						
						
					}
				}
			}
		}
		
		final StringBuffer result = new StringBuffer();
		for (final Assignment a : assignments) {
			result.append("\n   ");
			result.append(a.toString(useRFL));
		}
		
		if(junitFormat){
			result.append("\n");
			result.append(createOldMap(objects)+"\n");
			result.append(createBoolSet()+"\n");
			result.append(createIntSet()+"\n");
			result.append(createObjSet(heap)+"\n");			
		}
				
		
		return result.toString();
	}
	
	private String createOldMap(Set<String> objNames){
		String result = "\n"+TAB+"Map<Object,Object> "+OLDMap+" = new HashMap<Object,Object>()";
		for(String o : objNames){
			result += "\n"+TAB+OLDMap+".put("+getPreName(o)+","+o+");";
		}
		return result;
	}
	
	private String getPreName(String val) {
		return OracleGenerator.PRE_STRING+val;
	}
	private String createObjectName(final ObjectVal o) {
		return o.getName().replace("#", "_");
	}
	
	private String getTypeOfValue(Heap heap, Model m, String val){
		String type = "int";
		if (val.equals("true") || val.equals("false")) {
			type = "boolean";
		} else if (val.startsWith("#o")) {
			final ObjectVal o = getObject(heap, val);
			if (o != null) {
				if (val.equals("#o0")){
/*				        && m.getTypes().getOriginalConstantType(c) != null) {
					type = m.getTypes().getOriginalConstantType(c)
					        .name().toString();
					        */
					type = "Object";
				} else {
					//System.out.println(o);
					type = o.getSort().name().toString();
				}
			} else {
				type = "Object";
			}			
		}
		return type;
	}

	private String getDummyClassNameFor(Sort sort) {
		final JavaInfo jinfo = services.getJavaInfo();
		final KeYJavaType kjt = jinfo.getKeYJavaType(sort);
		return kjt.getName() + DummyPostfix;
	}

	private String getFilePrefix(String className) {
		String res = "/** This is a test driver generated by KeY "+Main.VERSION+" (www.key-project.org). \n" +
		          " * Possible use cases: \n" +
		          " *  1. Compile and execute the main method with a JML runtime checker to test the method under test.\n" +
		          " *  2. Use a debuger to follow the execution of the method under test.\n" +
		          " * @author gladisch\n" +
		          " * @author herda\n" +
		          " */\n";
		if (junitFormat) {
			res += "import junit.framework.*;\n"
					+ "import java.util.List;\n"
					+ "import java.util.LinkedList;\n"
					+ "import java.util.Map;\n"
					+ "import java.util.HashMap;\n"
					+ " public class " + className
			        + " extends junit.framework.TestCase {\n\n" + " public "
			        + className + "(){}\n"
			        + " public static junit.framework.TestSuite suite () {\n"
			        + "   junit.framework.TestSuite suiteVar;\n"
			        + "   suiteVar=new junit.framework.TestSuite (" + className
			        + ".class);\n" + "   return  suiteVar;\n" + " }\n";
		} else {
			res += "public class " + className + "{ \n\n" + " public "
			        + className + "(){}\n";
		}
		return res;
	}

	private StringBuffer getMainMethod(String className, int i) {
		final StringBuffer res = new StringBuffer();
		res.append(" public static void  main (java.lang.String[]  arg) {\n"
		        + "   " + className + " testSuiteObject;\n"
		        + "   testSuiteObject=new " + className + " ();\n\n");
		for (int j = 0; j < i; j++) {
			res.append("   testSuiteObject.testcode" + j + "();\n");
		}
		if (i == 0) {
			res.append("   //Warning:no test methods were generated.\n");
		}
		res.append(" }");
		return res;
	}

	private ObjectVal getObject(Heap h, String name) {
		if (h == null) {
			return null;
		}
		for (final ObjectVal o : h.getObjects()) {
			if (o.getName().equals(name)) {
				return o;
			}
		}
		return null;
	}
	
	private String createBoolSet(){
		
		StringBuffer res = new StringBuffer();		
		//bool
		String allbool = ALL_BOOLS;
		res.append('\n');
		res.append(TAB+"List<Boolean> "+allbool +"= new LinkedList<Boolean>();\n");
		res.append(TAB+allbool+".add(true);\n");
		res.append(TAB+allbool+".add(false);\n");
		return res.toString();		
	}
	
	private String createIntSet(){
		
		StringBuffer res  = new StringBuffer();
		long size = ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings().intBound;
		
		long low = (long) - Math.pow(2, size-1);
		long hi = (long) (Math.pow(2, size-1)-1);
		
		String allint = ALL_INTS;
		res.append(TAB+"List<Integer> "+allint +"= new LinkedList<Integer>();\n");
		
		for(long i = low; i <= hi; i++ ){			
			res.append(TAB+allint+".add("+i+");\n");			
		}	
		
		return res.toString();		
	}
	
	private String createObjSet(Heap h){
		
		StringBuffer res  = new StringBuffer();		
		
		res.append(TAB+"List<Object> "+ALL_OBJECTS +"= new LinkedList<Object>();\n");
		
		for(ObjectVal o : h.getObjects()){
			String name = o.getName();
			if(name.equals("#o0")){
				continue;
			}
			name = name.replace("#", "_");
			res.append(TAB+ALL_OBJECTS+".add("+name+");\n");
			
		}			
		
		return res.toString();		
	}
	
	

	public String getSafeType(Sort sort) {
		if (sort == null) {
			return "java.lang.Object"; // TODO:Hopefully this is correct
		} else if (sort.isAbstract()) {
			return buildDummyClassForAbstractSort(sort);
		} else {
			return sort.name().toString();
		}
	}

	private String getTestMethodSignature(int i) {
		final String sig = " public void  testcode" + i + "()";
		if (junitFormat) {
			return "@Test\n" + sig;
		} else {
			return sig;
		}
	}

	public boolean isJunit() {
		return junitFormat;
	}

	protected boolean isNumericType(String type) {
		return type.equals("byte") || type.equals("short")
		        || type.equals("int") || type.equals("long")
		        || type.equals("float") || type.equals("double");
	}

	protected boolean isPrimitiveType(String type) {
		return isNumericType(type) || type.equals("boolean")
		        || type.equals("char");
	}

	public void setJUnit(boolean junit) {
		junitFormat = junit;
	}

	public void setLogger(TGInfoDialog logger) {
		this.logger = logger;
	}

	protected String translateValueExpression(String val) {
		if (val.contains("/")) {
			val = val.substring(0, val.indexOf("/"));
		}
		if (val.equals("#o0")) {
			return "null";
		}
		val = val.replace("|", "");
		val = val.replace("#", "_");
		return val;
	}

	public void writeToFile(String file, StringBuffer sb) {
		try {
			final File dir = new File(directory + modDir);
			if (!dir.exists()) {
				dir.mkdirs();
			}
			final File pcFile = new File(dir, file);
			System.out.println("Writing file:"+pcFile.toString());
			final FileWriter fw = new FileWriter(pcFile);
			final BufferedWriter bw = new BufferedWriter(fw);
			bw.write(sb.toString());
			bw.close();
			// create a temporary file
			// File logFile=new File("TestGeneric"+fileCounter+".java");
			// BufferedWriter writer = new BufferedWriter(new
			// FileWriter(logFile));
			// writer.write (sb.toString());
			// Close writer
			// writer.close();
		} catch (final Exception e) {
			e.printStackTrace();
		}
	}
}
