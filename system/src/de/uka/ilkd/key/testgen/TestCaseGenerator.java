package de.uka.ilkd.key.testgen;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.gui.actions.TestGenerationAction;
import de.uka.ilkd.key.gui.smt.TGInfoDialog;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.model.Heap;
import de.uka.ilkd.key.smt.model.Model;
import de.uka.ilkd.key.smt.model.ObjectVal;

/**
 * @author gladisch
 * @author herda 
 */
public class TestCaseGenerator {

	Services services;
	Proof proof;
	static int fileCounter=0;
	boolean junitFormat;

	private static final String DONT_COPY = "aux"; //Classes of the Java environment needed by KeY can be placed in this subdirectory.
	private final String dontCopy;
	protected final String modDir;
	protected final String directory;
	private TGInfoDialog logger;
	String fileName;
	String MUTName;

	private Map<Sort,StringBuffer> sortDummyClass;

	final String DummyPostfix = "DummyImpl";


	public TestCaseGenerator() {
		super();
		this.proof = TestGenerationAction.originalProof;
		this.services = proof.getServices();
		junitFormat = false;
		modDir = proof.getJavaModel().getModelDir();
		dontCopy = modDir + File.separator + DONT_COPY;
		this.directory = System.getProperty("user.home") + File.separator + "testFiles";
		sortDummyClass = new HashMap<Sort,StringBuffer>();
		MUTName = "";
	}

	private boolean filterVal(String s){
		if(s.startsWith("#a")||s.startsWith("#s")||s.startsWith("#h")||s.startsWith("#l")||s.startsWith("#f")){
			return false;
		}
		else{
			return true;
		}
	}



	public void setLogger(TGInfoDialog logger) {
		this.logger = logger;
	}

	private ObjectVal getObject(Heap h,String name){
		if(h==null){
			return null;
		}
		for(ObjectVal o : h.getObjects()){
			if(o.getName().equals(name)){
				return o;
			}
		}
		return null;
	}

	public String generateJUnitTestSuite(Collection<SMTSolver> problemSolvers){
		MUTName = "";
		fileName = "TestGeneric"+fileCounter;
		String mut = getMUT(); //sets MUTName as side-effect
		if(mut==null){
			mut = "<method under test> //Manually write a call to the method under test, because KeY could not determine it automatically.";
		}else{
			fileName += "_"+MUTName;
		}
		StringBuffer testSuite = new StringBuffer();
		testSuite.append(getFilePrefix(fileName) + "\n");

		StringBuffer testMethods = new StringBuffer();
		int i = 0;
		for(SMTSolver solver : problemSolvers){
			if(solver.getQuery()!=null){
				Model m = solver.getQuery().getModel();
				if(m!=null && !m.isEmpty()){
					logger.write("Generate test Case: "+i);
					testMethods.append(getTestMethodSignature(i)+"{\n");
					testMethods.append("   //Test preamble: creating objects and intializing test data"+generateTestCase(m)+"\n\n");
					testMethods.append("   //Calling the method under test\n   "+mut+"; \n");
					testMethods.append(" }\n\n");

					i++;
				}
			}
		}

		testSuite.append(getMainMethod(fileName, i)+"\n\n");

		testSuite.append(testMethods);

		testSuite.append("\n}");

		System.out.println("Writing test file to:"+directory+modDir);
		writeToFile(fileName + ".java", testSuite);
		logger.write("Writing test file to:"+directory+modDir+File.separator+fileName);

		exportCodeUnderTest();

		createDummyClasses();

		createOpenJMLShellScript();

		fileCounter++;
		return testSuite.toString();

	}

	public String generateJUnitTestCase(Model m){
		fileName = "TestGeneric"+fileCounter;
		String mut = getMUT();//sets MUTName as side-effect
		if(mut==null){
			mut = "<method under test> //Manually write a call to the method under test, because KeY could not determine it automatically.";
		}else{
			fileName += "_"+MUTName;
		}
		StringBuffer testCase = new StringBuffer();
		testCase.append(getFilePrefix(fileName) + "\n");
		testCase.append(getMainMethod(fileName, 1)+"\n\n");
		testCase.append(getTestMethodSignature(0)+"{\n");
		testCase.append("   //Test preamble: creating objects and intializing test data"+generateTestCase(m)+"\n\n");
		testCase.append("   //Calling the method under test\n   "+mut+"; \n");
		testCase.append("}\n}");

		System.out.println("Writing test file to:"+directory+modDir);
		logger.write("Writing test file to:"+directory+modDir+File.separator+fileName);
		writeToFile(fileName + ".java", testCase);
		exportCodeUnderTest();

		createDummyClasses();

		createOpenJMLShellScript();

		fileCounter++;
		return testCase.toString();
	}

	public void writeToFile(String file, StringBuffer sb){
		try
		{

			final File dir = new File(directory + modDir);
			if (!dir.exists()) {
				dir.mkdirs();
			}
			final File pcFile = new File(dir, file);
			String path = pcFile.getAbsolutePath();
			final FileWriter fw = new FileWriter(pcFile);
			final BufferedWriter bw = new BufferedWriter(fw);
			bw.write(sb.toString());
			bw.close();


			//create a temporary file
			//		    File logFile=new File("TestGeneric"+fileCounter+".java");
			//		    BufferedWriter writer = new BufferedWriter(new FileWriter(logFile));
			//		    writer.write (sb.toString());

			//Close writer
			//writer.close();
		} catch(Exception e)
		{
			e.printStackTrace();
		}
	}


	private String getFilePrefix(String className){
		String res = "//This is a test driver generated by KeY 2.2. \n" +
				"//Possible use cases: \n" +
				"//  1. Compile and execute the main method with a JML runtime checker to test the method under test.\n" +
				"//  2. Use a debuger to follow the execution of the method under test.\n\n\n";
		if(junitFormat){
			res += "import junit.framework.*;\n"
					+ " public class "+className+" extends junit.framework.TestCase {\n\n"
					+ " public "+className+"(){}\n"
					+ " public static junit.framework.TestSuite suite () {\n"
					+ "   junit.framework.TestSuite suiteVar;\n"
					+ "   suiteVar=new junit.framework.TestSuite ("+className+".class);\n"
					+ "   return  suiteVar;\n" 
					+ " }\n";
		}else{
			res += "public class "+className+"{ \n\n"
					+ " public "+className+"(){}\n";			
		}
		return res;
	}

	private String getTestMethodSignature(int i){
		return " public void  testcode"+i+"()";
	}
	private StringBuffer getMainMethod(String className, int i){
		StringBuffer res = new StringBuffer();
		res.append( " public static void  main (java.lang.String[]  arg) {\n"
				+"   "+className+" testSuiteObject;\n"
				+"   testSuiteObject=new "+className+" ();\n\n");
		for(int j=0;j<i;j++){
			res.append("   testSuiteObject.testcode"+j+"();\n");
		}
		if(i==0)
			res.append("   //Warning:no test methods were generated.\n");
		res.append(" }");
		return res;
	}

	public String generateTestCase(Model m){

		List<Assignment> assignments = new LinkedList<Assignment>();

		Heap heap = null;
		for(Heap h : m.getHeaps()){
			if(h.getName().equals("heap")){
				heap = h;
				break;
			}
		}		

		if(heap!=null){
			//create objects
			for(ObjectVal o : heap.getObjects()){
				if(o.getName().equals("#o0")){
					continue;
				}
				String type = getSafeType(o.getSort());

				String right;				
				if(type.endsWith("[]")){
					right = "new "+type.substring(0, type.length()-2)+"["+o.getLength()+"]";
				}
				else{
					right = "new "+type+"()";
				}
				assignments.add(new Assignment(type, o.getName().replace("#", "_"), right));


			}			
		}
		//init constants
		for(String c : m.getConstants().keySet()){
			String val = m.getConstants().get(c);

			if(filterVal(val) && !c.equals("null")){

				String type = "int";
				if(val.equals("true")||val.equals("false")){
					type = "boolean";
				}
				else if(val.startsWith("#o")){
					ObjectVal o = getObject(heap, val);
					if(o!=null){
						if(val.equals("#o0") && m.getTypes().getOriginalConstantType(c)!=null){
							type = m.getTypes().getOriginalConstantType(c).name().toString();
						}
						else{
							type = o.getSort().name().toString();
						}


					}
					else{
						type = "Object";
					}
					type = "/*@ nullable */ " + type;
				}
				val = translateValueExpression(val);
				assignments.add(new Assignment(type,c,val));
			}
		}

		//init fields
		if(heap!=null){

			for(ObjectVal o : heap.getObjects()){
				if(o.getName().equals("#o0")){
					continue;
				}

				String name = o.getName().replace("#", "_");

				for(String f : o.getFieldvalues().keySet()){
					if(f.contains("<") || f.contains(">")){
						continue;
					}
					String fieldName = f.substring(f.lastIndexOf(":")+1);
					fieldName = fieldName.replace("|", "");
					String val = o.getFieldvalues().get(f);
					val = translateValueExpression(val);
					assignments.add(new Assignment(name+"."+fieldName, val));
				}
				if(o.getSort()!=null && o.getSort().name().toString().endsWith("[]")){
					for(int i = 0; i < o.getLength(); i++){
						String fieldName = "["+i+"]";
						String val = o.getArrayValue(i);						
						val = translateValueExpression(val);
						assignments.add(new Assignment(name+fieldName, val));
					}
				}

			}			
		}


		StringBuffer result = new StringBuffer();
		for(Assignment a : assignments){
			result.append(a.toString());
		}



		return result.toString();
	}

	protected String translateValueExpression(String val){
		if(val.contains("/")){
			val = val.substring(0, val.indexOf("/"));
		}
		if(val.equals("#o0")) return "null";
		val = val.replace("|", "");
		val = val.replace("#", "_");
		return val;
	}

	public String getSafeType(Sort sort){
		if(sort==null){
			return "java.lang.Object"; //TODO:Hopefully this is correct
		}else if(sort.isAbstract()){
			return buildDummyClassForAbstractSort(sort);
		}else{
			return sort.name().toString();
		}
	}

	private String getDummyClassNameFor(Sort sort){
		JavaInfo jinfo = services.getJavaInfo();
		KeYJavaType kjt = jinfo.getKeYJavaType(sort); 
		return kjt.getName()+DummyPostfix;
	}

	protected boolean isNumericType(String type){
		return type.equals("byte") || type.equals("short") || type.equals("int") || 
				type.equals("long") || type.equals("float") || type.equals("double");
	}

	protected boolean isPrimitiveType(String type){
		return isNumericType(type) || type.equals("boolean") || type.equals("char");
	}

	protected String buildDummyClassForAbstractSort(Sort sort){

		JavaInfo jinfo = services.getJavaInfo();
		KeYJavaType kjt = jinfo.getKeYJavaType(sort); 
		String className = getDummyClassNameFor(sort);
		if(sortDummyClass.containsKey(sort)) return className;

		StringBuffer sb = new StringBuffer();
		sortDummyClass.put(sort, sb); //Put the string buffer as soon as possible, due to possible recursive calls of this method.

		sb.append("import "+sort.declarationString()+";\n\n");
		sb.append("class "+className + " implements "+sort.declarationString()+"{\n"); //TODO:extends or implements depending if it is a class or interface.
		sb.append(" public "+className+"(){ };\n");  //default constructor

		Iterator<IProgramMethod> methods = jinfo.getAllProgramMethods(kjt).iterator();		
		while(methods.hasNext()){
			IProgramMethod m = methods.next();
			if(m.getFullName().indexOf('<')>-1) continue;
			if(m.isPrivate() || m.isFinal() || !m.isAbstract()) continue;
			sb.append(" ");
			MethodDeclaration md = m.getMethodDeclaration();
			//sb.append(md.toString()+ "\n");
			if(m.isProtected())
				sb.append("protected ");
			if(m.isPublic())
				sb.append("public ");
			if(m.isFinal())
				sb.append("final "); //Is this possible?
			if(m.isStatic())
				sb.append("static ");
			if(m.isSynchronized())
				sb.append("synchronized ");

			if(md.getTypeReference()==null)
				sb.append("void ");
			else
				sb.append(md.getTypeReference().toString() + " ");

			sb.append(m.getName()+"(");
			Iterator<ParameterDeclaration> pdIter = md.getParameters().iterator();
			int varcount =0;
			while(pdIter.hasNext()){
				ParameterDeclaration pd = pdIter.next();
				if(pd.isFinal())
					sb.append("final ");

				if(pd.getTypeReference()==null)
					sb.append("void /*unkown type*/ ");
				else 
					sb.append(pd.getTypeReference().toString()+ " ");

				if(pd.getVariables().isEmpty())
					sb.append("var"+varcount);
				else
					sb.append(pd.getVariables().iterator().next().getFullName());

				if(pdIter.hasNext())
					sb.append(", ");
				varcount ++;
			}
			sb.append(")");
			if(md.getThrown()!=null){
				sb.append(" throws "+md.getThrown().getTypeReferenceAt(0)+ " \n ");
			}

			if(md.getTypeReference()==null){
				sb.append("{ };");
			}else{
				String type = md.getTypeReference().toString();
				if(isNumericType(type) ){					
					sb.append("{ return 0;}");
				} else if( type.equals("boolean")){
					sb.append("{ return true;}");
				} else if( type.equals("char") ){
					sb.append("{ return 'a';}");
				}else {
					boolean returnNull=true;
					try{
						String retType = md.getTypeReference().getKeYJavaType().getSort().name().toString();
						if(retType.equals("java.lang.String")){
							sb.append("{ return \""+className+"\";}");
							returnNull=false;
						}
					}catch(Exception e){returnNull=true;}

					if(returnNull)
						sb.append("{ return null;}");
				}
			} 
			sb.append("\n");
		}
		sb.append("}");
		//System.out.println("--------------------\n"+sb.toString());
		return className;
	}

	public String getMUT(){
		System.out.println("Selected proof name:"+proof.name());

		Node root = proof.root();
		Sequent seq = root.sequent();
		Semisequent succ = seq.succedent();
		Iterator<SequentFormula> it = succ.iterator();
		String res = null;
		while(it.hasNext()){
			SequentFormula sf = it.next();
			Term form = sf.formula();
			res = findMUTInFormula(form);
			if(res!=null) break;
		}
		return res;
	}

	private String findMUTInFormula(Term form){
		JavaBlock jb = form.javaBlock();
		if(jb==null || jb.isEmpty()){
			for(int i = 0 ; i<form.arity();i++){
				String res = findMUTInFormula(form.sub(i));
				if(res!=null) return res;
			}
		}
		else {
			//System.out.println("---JavaBlock found:"+jb);
			JavaProgramElement jpe = jb.program();
			String res = findMUTInJavaPE(jpe);			
			if(res!=null) return res;
		}
		return null;
	}

	private String findMUTInJavaPE(JavaProgramElement jpe){
		if(jpe instanceof JavaNonTerminalProgramElement){
			JavaNonTerminalProgramElement jntpe = (JavaNonTerminalProgramElement) jpe;
			//System.out.println("JavaNonTerminalProgramElement " + jntpe.toSource());
			for(int i = 0; i<jntpe.getChildCount(); i++){
				ProgramElement pe = jntpe.getChildAt(i);
				//System.out.println("ProgramElement ("+pe.getClass()+") "+pe);
				if(pe instanceof MethodBodyStatement){
					MethodBodyStatement mbs = (MethodBodyStatement)pe;
					MUTName = mbs.getMethodReference().getMethodName().toString();

					String methodCall = mbs.toString();
					//System.out.println("Method call:"+methodCall);
					int idx = methodCall.indexOf("@");
					if(idx>0){
						methodCall = methodCall.substring(0, idx);
					}
					//System.out.println("Method call:"+methodCall);
					//Parameters. The following is some dirty string magic that removes leading "_" of arguments.
					//The correct solution is to translate the update in front of the modality and declare missing varialbes.

					Iterator<? extends Expression> argIter = mbs.getArguments().iterator();
					HashMap<String,String> newArgs = new HashMap();
					while(argIter.hasNext()){
						Expression ex = argIter.next();
						if(ex instanceof IProgramVariable){
							String progVar = ((IProgramVariable) ex).name().toString();
							if(progVar.startsWith("_")){								
								String newProgVar = progVar.substring(1);
								newArgs.put(progVar, newProgVar);
								//System.out.println("Replace:"+progVar+ "  by:"+newProgVar);
							}
						}
					}
					idx = methodCall.indexOf("(");
					String mc1 = methodCall.substring(0,idx);
					String mc2 = methodCall.substring(idx);
					for(String oldVar: newArgs.keySet()){						
						mc2 = mc2.replace(oldVar, newArgs.get(oldVar));
					}
					//System.out.println("mc1:"+mc1+"  mc2:"+mc2);
					methodCall = mc1 + mc2 ;

					//Result variable
					IProgramVariable resultVar = mbs.getResultVariable();
					if(resultVar!=null){
						Sort s= resultVar.sort();						
						methodCall = getSafeType(s) + " " + methodCall;
						String resType = s.name().toString();
						if(!isPrimitiveType(resType)){
							methodCall = "/*@ nullable @*/ " + methodCall;
						}
					}

					//System.out.println("Method call:"+methodCall);
					return methodCall;

				}else if(pe instanceof JavaProgramElement){
					String res = findMUTInJavaPE((JavaProgramElement)pe);
					if(res!=null) return res;
				}

			}
		}
		return null;
	}

	protected void createDummyClasses(){
		for(Sort s:sortDummyClass.keySet()){
			StringBuffer sb=sortDummyClass.get(s);
			String file = getDummyClassNameFor(s) + ".java";
			writeToFile(file,sb);
		}	
	}
	//TODO: in future remove this string and provide the file in the KeY-project
	final String compileWithOpenJML="#!/bin/bash\n\n"+
			"if [ -e \"openjml.jar\" ]\n"+
			"then\n"+
			"   java -jar openjml.jar -cp \".\" -rac *.java\n"+
			"else\n"+
			"   echo \"openjml.jar not found!\"\n"+
			"   echo \"Download openJML from http://sourceforge.net/projects/jmlspecs/files/\"\n"+
			"   echo \"Copy openjml.jar into the directory with test files.\"\n"+
			"fi\n";

	//TODO: in future remove this string and provide the file in the KeY-project
	final String executeWithOpenJML="#!/bin/bash\n"+
			"if [ -e \"jmlruntime.jar\" ]\n"+
			"then"+
			"  if [ -e \"jmlspecs.jar\" ]\n"+
			"  then\n"+
			"   if [ \"$1\" = \"\" ] ; then\n"+
			"    echo \"Provide the test driver as an argument (without .java postfix). For example:\"\n"+
			"    echo \"  executeWithOpenJML.sh TestGeneric0 \"\n"+
			"    echo \"Make sure that jmlruntime.jar and jmlspecs.jar are in the\"\n"+
			"    echo \"current directory.\"\n"+
			"    quit\n"+
			"   else\n"+								
			"     java -cp jmlruntime.jar:jmlspecs.jar:. $1\n"+								
			"   fi\n"+
			"else\n"+
			"  echo \"jmlspecs.jar not found!\"\n"+
			"  echo \"Download openJML from http://sourceforge.net/projects/jmlspecs/files/\"\n"+
			"  echo \"Copy jmlspecs.jar into the directory with test files.\"\n"+
			"  quit\n"+
			"fi\n"+
			"else\n"+
			"   echo \"jmlruntime.jar not found!\"\n"+
			"   echo \"Download openJML from http://sourceforge.net/projects/jmlspecs/files/\"\n"+
			"   echo \"Copy jmlruntime.jar into the directory with test files.\"\n"+
			"   quit\n"+
			"fi\n";



	protected void createOpenJMLShellScript(){
		StringBuffer sb=new StringBuffer();
		String filestr = "compileWithOpenJML.sh";

		File file = new File(directory + modDir + File.separator + filestr);
		if (!file.exists()) {
			sb.append(compileWithOpenJML);
			writeToFile(filestr, sb);
		}

		filestr= "executeWithOpenJML.sh";
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

}
