package de.uka.ilkd.key.unittest;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.declaration.modifier.*;
import de.uka.ilkd.key.java.expression.*;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.expression.literal.*;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.abstraction.*;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.java.visitor.*;
import de.uka.ilkd.key.unittest.ppAndJavaASTExtension.*;
import de.uka.ilkd.key.util.*;
import de.uka.ilkd.key.visualdebugger.VisualDebugger;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.sort.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.soundness.TermProgramVariableCollector;
import de.uka.ilkd.key.rule.UpdateSimplifier;

import java.io.*;
import java.util.*;
    

/**
 * Generates a unittest for a given piece of code and a set of modelgenerators.
 */
public class TestGenerator{

    private StringWriter w;
    private Services serv;
    private JavaInfo ji;//It should be possible to get rid of JavaInfo entirely if all KeYJavaTypes are "replaced" by SyntacticalTypeRefs. This would make the class more independent from the type system known by in JavaInfo.

    private SyntacticalTypeRef testCase;
    private SyntacticalTypeRef testSuite;
    private SyntacticalTypeRef testTypeRef;
    private SyntacticalTypeRef stringBufferType;
    private KeYJavaType b;
    private KeYJavaType intType;
    private String fileName;
    private String path=null;
    private String resultName = "_oracleResult";

    private Random rand;

    private MethodDeclaration suiteMethod;

    private int mcounter=0;

    private MethodReference oracle = null;

    public static int counter = 0;

    private HashMap translatedFormulas;
    private String directory=System.getProperty("user.home")+ File.separator+"testFiles";
//    private HashMap array2length;

    /**
     * creates a TestGenerator instance for the given compilation unit
     * @param serv the Services
     * @param fileName the name of the unittest file this TestGenerator 
     * creates.
     */
    public TestGenerator(Services serv, String fileName){
	ji = serv.getJavaInfo();
	translatedFormulas = new HashMap();
//	array2length = new HashMap();
	this.fileName = fileName;
	w = new StringWriter();
	this.serv = serv;
	ExtList l = new  ExtList();
	l.add(new ProgramElementName(fileName));
    
	Type suiteType = new ClassDeclaration(l, new ProgramElementName(fileName), false);
        testTypeRef = new SyntacticalTypeRef(suiteType);
        
	testCase    = new SyntacticalTypeRef(
	                new ClassDeclaration(
	                        new ProgramElementName("TestCase"), 
	                        new ProgramElementName("junit.framework.TestCase")));
        testSuite   = new SyntacticalTypeRef(
                        new ClassDeclaration(
                                new ProgramElementName("TestSuite"), 
                                new ProgramElementName("junit.framework.TestSuite")));
        stringBufferType = new SyntacticalTypeRef(
                            new ClassDeclaration(
                                new ProgramElementName("StringBuffer"),
                                new ProgramElementName("java.lang.StringBuffer")));

	b = ji.getTypeByName("boolean"); //You can create a SyntacticalTypeRef for BooleanType as well if JavaInfo doesn't provide it (as it should be in a clean typesystem for JavaCard).
	intType = ji.getTypeByName("int"); //You can create a SyntacticalTypeRef for Integer type as well if JavaInfo doesn't provide it (as it should be in a clean typesystem for JavaCard).
	suiteMethod = createSuiteMethod();
	rand = new Random();
    }
    
    
    public TestGenerator(Services serv, String fileName, String directory){
      this(serv, fileName);
      if (directory!=null)
          this.directory = directory;
    }

    /**
     * Creates the class declaration of the unit test that should be exported
     * to a file.
     */
    private ClassDeclaration createSuiteClass(ExtList l){
	l.add(new Public());
	l.add(new Extends(testCase));
	l.add(new ProgramElementName(fileName));
	ClassDeclaration result = 
	    new ClassDeclaration(l, new ProgramElementName(fileName), false);
//	FieldReplaceVisitor frv = new FieldReplaceVisitor(result);
//	frv.start();
	return result;
    }

    private KeYJavaType getArrayTypeAndEnsureExistence(KeYJavaType baseType,
                                                       int dim){
        final JavaInfo ji = serv.getJavaInfo();
        Sort as = ArraySortImpl.getArraySortForDim(
            baseType.getSort(), dim, 
            ji.getJavaLangObjectAsSort(),
            ji.getJavaLangCloneableAsSort(),
	    ji.getJavaIoSerializableAsSort());
        KeYJavaType kjt = ji.getKeYJavaType(as);
        if(kjt == null || baseType.getSort().toString().equals("int")){
            JavaBlock jb = ji.readJavaBlock("{"+as+" v;}");
            return ((VariableDeclaration) 
                    ((StatementBlock) jb.program()).getChildAt(0)).
		getTypeReference().getKeYJavaType();
        }
        return kjt;
    }

    private KeYJavaType getBaseType(KeYJavaType arrayType){
	return ((ArrayType) arrayType.getJavaType()).getBaseType().
	    getKeYJavaType();
    }

    /** Creates a method of the form: 
     *  public void <name>(){
     *    &lt pv-decls for v0,...,vl &gt;
     *    testData0 = {d_00,...,d_0k};
     *    ...
     *    testDataj = {d_j0,...,d_jk};
     *    for(int i=0; i<testData0.length; i++){
     *        ...
     *        l0 = testData0[i];
     *        ...
     *        lj = testDataj[i];
     *        <code>
     *        java.lang.StringBuffer buffer;
     *        buffer = new java.lang.StringBuffer ();
     *	      boolean result = testOracle(v0,..., vl, buffer);
     *        assertTrue (&lt String &gt, result);
     *    }
     *  }
     *  Where &lt String &gt contains the assignments of l0,...,lj in this
     *  iteration and the results the oracles for the subformulas of post
     *  have provided so far.
     *
     */
    private MethodDeclaration createTestMethod(Statement code[], Term post, 
					       Expression[][] testLocation,
					       Expression[][] testData,
//					       ProgramVariable[] pvs,
					       ProgramVariable[] pvsNotDecl,
					       String name, ExtList children,
					       ModelGenerator mg,
					       EquivalenceClass[] testLocEqvs){
	ListOfStatement s = SLListOfStatement.EMPTY_LIST;
	// declare and initialize program variables
	for(int i=0; i<pvsNotDecl.length; i++){
	    VariableSpecification varSpec = null;
	    if(pvsNotDecl[i].getKeYJavaType().getSort().extendsTrans(
		   serv.getTypeConverter().getIntegerLDT().targetSort())){
		varSpec = 
		    new VariableSpecification(
			pvsNotDecl[i], new TypeCast(
			    new IntLiteral(0), new TypeRef(
				pvsNotDecl[i].getKeYJavaType())),
			pvsNotDecl[i].getKeYJavaType());
	    }else if(pvsNotDecl[i].getKeYJavaType().getSort() == b.getSort()){
		varSpec = 
		    new VariableSpecification(pvsNotDecl[i], 
					      BooleanLiteral.TRUE,
					      pvsNotDecl[i].getKeYJavaType());
	    }else{
/*		varSpec = 
		    new VariableSpecification(
			pvsNotDecl[i], new New(
			    new Expression[0], 
			    new TypeRef(pvsNotDecl[i].getKeYJavaType()), 
			    null),
			    pvsNotDecl[i].getKeYJavaType());*/
		varSpec = new VariableSpecification(
		    pvsNotDecl[i], NullLiteral.NULL, 
		    pvsNotDecl[i].getKeYJavaType());
	    }
	    LocalVariableDeclaration lvd = new LocalVariableDeclaration(
		new TypeRef(pvsNotDecl[i].getKeYJavaType()), 
		varSpec);
	    s = s.append(lvd);
	}

	// put test data in array
	ProgramVariable[] testArray = 
	    new ProgramVariable[testLocation.length];
	boolean singleTuple = singleTuple(testData);
	for(int i=0; i<testData.length; i++){
	    KeYJavaType kjt = testLocEqvs[i].getKeYJavaType();
	    if(singleTuple){
		Expression testDatum;
		if(testData[i][0] != null){
		    testDatum = new TypeCast(testData[i][0], new TypeRef(kjt));
		}else{
		    testDatum = new TypeCast(new IntLiteral(rand.nextInt()), 
					     new TypeRef(kjt));
		}
		testArray[i] = new LocationVariable(
		    new ProgramElementName("testData"+i), kjt); 
		VariableSpecification vs = 
		    new VariableSpecification(testArray[i], testDatum, 
					      kjt.getJavaType());
		s = s.append(new LocalVariableDeclaration(
				 new TypeRef(kjt), vs));
	    }else{
		KeYJavaType akjt = getArrayTypeAndEnsureExistence(kjt, 1);
		ExtList ai = new ExtList();
		for(int j = 0; j<testData[i].length; j++){
		    ExtList partj = new ExtList();
		    if(testData[i][j] != null){
			ai.add(new TypeCast(testData[i][j], new TypeRef(kjt)));
		    }else{
			ai.add(new TypeCast(new IntLiteral(rand.nextInt()), 
					    new TypeRef(kjt)));
		    }
		}
		testArray[i] = new LocationVariable(
		    new ProgramElementName("testData"+i), akjt); 
		ExtList aType = new ExtList();
		aType.add(new TypeRef(kjt));
		NewArray init = 
		    new NewArray(aType, kjt, new ArrayInitializer(ai),
				 1);
		VariableSpecification vs = 
		    new VariableSpecification(testArray[i], init, 
					      akjt.getJavaType());
		s = s.append(new LocalVariableDeclaration(
				 new TypeRef(akjt), vs));
	    }
	}
	ArrayOfExpression arg = new ArrayOfExpression();
	ExtList l = new ExtList();
	l.add(new ProgramElementName(name));
	l.add(new Public());
	Statement[] ib = new Statement[6+code.length];

	ProgramVariable partCounter = 
	    new LocationVariable(new ProgramElementName("testDataCounter"), 
				intType);
	ProgramVariable length = 
	    new LocationVariable(new ProgramElementName("length"), intType);

	// assignments of test data to locations + initialization of 
	// object references
	ListOfStatement assignments = SLListOfStatement.EMPTY_LIST;

	// initialization of arrays and creation of test data assignments
	HashMap array2Cons = new HashMap();
	ListOfStatement testDataAssignments = SLListOfStatement.EMPTY_LIST;
	for(int i=0; i<testData.length; i++){
	    for(int k=0; k<testLocation[i].length; k++){
		Expression testDat = singleTuple ? (Expression) testArray[i] : 
		    (Expression) new ArrayReference(
			testArray[i], 
			new Expression[]{partCounter});
		if(testLocation[i][k] instanceof FieldReference &&
		   ((FieldReference) testLocation[i][k]).getProgramVariable().
		    name().toString().equals("length")){
		    KeYJavaType at = 
			((Expression) ((FieldReference) 
				       testLocation[i][k]).
			 getReferencePrefix()).getKeYJavaType(serv, null);
		    if(at.getSort() instanceof ArraySort){
			NewArray ar = 
			    new NewArray(new Expression[]{testDat},
					 new TypeRef(getBaseType(at)), at, 
					 null, 0);
//			array2length.put(((FieldReference) testLocation[i][k]).
//					 getReferencePrefix().toString(), 
//					 testDat);
			array2Cons.put(((FieldReference) testLocation[i][k]).
				       getReferencePrefix().toString(), ar);
			continue;
		    }
		}
		IndexReplaceVisitor irv = 
		    new IndexReplaceVisitor(testLocation[i][k], testLocation, 
					    singleTuple, partCounter, 
					    testArray, serv);
		irv.start();
		irv.result();
		testDataAssignments = testDataAssignments.append(	
		    assignmentOrSet((Expression) irv.result(),testDat, serv));
	    }
	}

	// initialization of other object references
	EquivalenceClass[] nonPrim = 
	    mg.getNonPrimitiveLocationEqvClasses();
	HashMap loc2cons = new HashMap();
	LinkedList locationsOrdered = new LinkedList();
	for(int i=0; i<nonPrim.length; i++){
	    SetOfTerm locs = nonPrim[i].getLocations();
	    IteratorOfTerm itt = locs.iterator();
	    if(!nonPrim[i].isNull()){
		Term nonPrimLocTerm = itt.next();
		Expression loc1 = translateTerm(nonPrimLocTerm, null, null);
		Expression cons;
		if(nonPrimLocTerm.sort() instanceof ArraySort){
		    cons = (Expression) array2Cons.get(loc1.toString());
		    if(cons == null){
			KeYJavaType locKJT = nonPrim[i].getKeYJavaType();
			cons = new NewArray(new Expression[]{
			    new IntLiteral(20)},
					    new TypeRef(getBaseType(locKJT)), 
					    locKJT, 
					    null, 0);
		    }
/*		    KeYJavaType locKJT =loc1.getKeYJavaType(serv, null);
		    ExtList aType = new ExtList();
		    aType.add(new TypeRef(locKJT));
		    cons = new NewArray(aType, locKJT, 
					new ArrayInitializer(new ExtList()),
					0);*/
		}else{
		    cons = new New(new Expression[0], 
				       new TypeRef(nonPrim[i].getKeYJavaType()),
				       null);
		}
		if(locs.size() > 1){
		    ProgramVariable pv = 
			new LocationVariable(new ProgramElementName("_init"+i),
					    nonPrim[i].getKeYJavaType());
		    VariableSpecification varSpec = new VariableSpecification(
			pv, cons, 
			nonPrim[i].getKeYJavaType());
		    assignments = 
			assignments.append(
			    new LocalVariableDeclaration(
				new TypeRef(nonPrim[i].getKeYJavaType()), 
				varSpec));
		    loc2cons.put(loc1, pv);
		    while(itt.hasNext()){
			Expression loc2 = translateTerm(itt.next(), null, null);
			addOrdered(loc2, locationsOrdered);
			loc2cons.put(loc2, pv);
		    }
		}else{
		    loc2cons.put(loc1, cons);
		}
		addOrdered(loc1, locationsOrdered);
	    }else{
		while(itt.hasNext()){
		    Term locTerm = itt.next();
		    if(locTerm.op() != Op.NULL){
			Expression loc2 = translateTerm(locTerm, null, null);
			addOrdered(loc2, locationsOrdered);
			loc2cons.put(loc2, NullLiteral.NULL);
		    }
		}
	    }
	}
	Iterator locIt = locationsOrdered.iterator();
	while(locIt.hasNext()){
	    Expression loc = (Expression) locIt.next();
	    Expression cons = (Expression) loc2cons.get(loc);
	    IndexReplaceVisitor irv = 
		new IndexReplaceVisitor(loc, testLocation, 
					singleTuple, partCounter, testArray, serv);
	    irv.start();
	    irv.result();
	    assignments = 
		assignments.append(assignmentOrSet(
				       (Expression) irv.result(), cons, serv));
	}

	assignments = assignments.append(testDataAssignments);
//	assignments = removeOutOfBounds(assignments);
	ib[0] = new StatementBlock(assignments.toArray());

	for(int i=0; i<code.length; i++){
	    ib[i+1] = code[i];
	}
	
	New cons = new New(new Expression[0], stringBufferType, null);
	SyntacticalProgramVariable buffer = 
	    new SyntacticalProgramVariable(new ProgramElementName("buffer"), 
	                                    stringBufferType.type);
	ib[code.length+1] = new LocalVariableDeclaration(
	                            stringBufferType, 
	                            new VariableSpecification(buffer, buffer.type));
	ib[code.length+2] = new CopyAssignment(buffer, cons);

	ProgramVariable result = 
	    new LocationVariable(new ProgramElementName(resultName), b);
	ib[code.length+3] = new LocalVariableDeclaration(new TypeRef(b), 
					    new VariableSpecification(result));
	MethodReference oracle = getOracle(post, buffer, children);
	ib[code.length+4] = new CopyAssignment(result, oracle);
/* This variable seems to be unused. JavaInfo methods cannot be applied on SyntacticalTypeReferences. This is on purpose.
 	ProgramMethod assertTrue = 
	    ji.getProgramMethod(testCase, "assertTrue", 
				SLListOfKeYJavaType.EMPTY_LIST.
				append(ji.getKeYJavaTypeByClassName(
					   "java.lang.String")).append(b),
				testCase);
*/	Expression failure = 
	    new StringLiteral("\\nPost evaluated to false.\\n"+
			      "Variable/Location Assignments:\\n");
	for(int i=0; i<testLocation.length; i++){
	    for(int j=0; j<testLocation[i].length; j++){
		Expression assignment = 
		    new Plus(new StringLiteral("  "+
					       testLocation[i][j].toString()+
					       " = "),
			     singleTuple ? (Expression) testArray[i]
			     : (Expression) new ArrayReference(
				 testArray[i], 
				 new Expression[]{partCounter}));
		failure = new Plus(failure, assignment);
	    }
	}
	Expression str = new Plus(
	    new StringLiteral("\\nEvaluation of subformulas so far: "), 
	    new MethodReference(new ArrayOfExpression(), 
				new ProgramElementName("toString"),
				buffer));
	str = new Plus(failure, str);
	ib[code.length+5] = new MethodReference(new ArrayOfExpression(
				       new Expression[]{str, result}), 
				   new ProgramElementName("assertTrue"),
				   null);
	Statement body = new StatementBlock(ib);
	
	// nested loops for executing the tested code with every possible 
	// combination of testdata in each partition  
	if(!singleTuple){
/*	    for(int i=0; i<testData.length; i++){
		VariableSpecification counterSpec = 
		    new VariableSpecification(lCounter[i], new IntLiteral(0), 
					      intType);
		LocalVariableDeclaration counterDecl = 
		    new LocalVariableDeclaration(new TypeRef(intType),
						 counterSpec);
		Expression guard = 
		    new LessThan(lCounter[i], new FieldReference(
				     length, new ArrayReference(
					 testArray[i], 
					 new Expression[]{partCounter})));
		Expression update = new PostIncrement(lCounter[i]);
		body = new For(new LoopInitializer[]{counterDecl}, guard, 
			       new Expression[]{update}, body);
			       }*/
	    // loop over the number of partitions
//	    int partCount = testData.length==0? 1 : testData[0].length;
	    VariableSpecification counterSpec = 
		new VariableSpecification(partCounter, new IntLiteral(0), 
					  intType);
	    LocalVariableDeclaration counterDecl = 
		new LocalVariableDeclaration(new TypeRef(intType),counterSpec);
	    Expression guard = 
		new LessThan(partCounter, testData.length==0 ? 
			     (Expression) new IntLiteral(1) : 
			     (Expression) new FieldReference(
				 length, testArray[0]));
//	    Expression guard = 
//		new LessThan(partCounter, new IntLiteral(partCount));
	    body = new For(new LoopInitializer[]{counterDecl}, guard,
	            new Expression[]{new PostIncrement(partCounter)} , body);
	}
	
	s = s.append(body);
	StatementBlock mBody = new StatementBlock(s.toArray());
	FieldReplaceVisitor frv = new FieldReplaceVisitor(mBody, serv);
	frv.start();
	l.add(frv.result());
	l.add(new Comment("\n  Covered execution trace:\n"+
			  mg.getExecutionTrace()));
	MethodDeclaration tm = new MethodDeclaration(l, false);
   
        if (VisualDebugger.isDebuggingMode()){
            VisualDebugger.getVisualDebugger().addTestCase(fileName, name, mg.getOriginalNode());
        }
            
	return tm;
    }

    private void addOrdered(Expression e, LinkedList l){
	for(int i=0; i<l.size(); i++){
	    if(depth((Expression) l.get(i)) > depth(e)){
		l.add(i, e);
		return;
	    }
	}
	l.add(e);
    }

    private boolean singleTuple(Expression[][] e){
	if(0<e.length){
	    return e[0].length == 1;
	}
	return true;
    }

    /**
     * Returns the depth, i.e. the length of the reference prefix of an
     * expression.
     */
    private int depth(Expression e){
	if((e instanceof FieldReference) && 
	   (((FieldReference) e).getReferencePrefix() instanceof 
	    Expression)){
	    return 1+depth((Expression) 
			   ((FieldReference) e).getReferencePrefix());
	}else if((e instanceof ArrayReference) &&
		 (((ArrayReference) e).getReferencePrefix() instanceof 
		  Expression)){
	    return depth((Expression) 
			 ((ArrayReference) e).getReferencePrefix())+1;
	}
	return 0;
    }

    /**
     * Generates either an assignment statement lhs = rhs; or a method call
     * statement for the appropriate set method in the case that
     * lhs is a field reference.
     */
    public static Statement assignmentOrSet(Expression lhs, Expression rhs,
					    Services serv){
	if(lhs instanceof FieldReference){
	    ProgramVariable pv = ((FieldReference) lhs).getProgramVariable();
	    String typeName = pv.getKeYJavaType().getName();
	    typeName = PrettyPrinter.getTypeNameForAccessMethods(typeName);
	    KeYJavaType kjt = pv.getContainerType();
	    String pvName = pv.name().toString();
	    pvName = pvName.substring(pvName.lastIndexOf(":")+1);
	    String methodName =	"_set" + pvName+typeName;
	    ListOfKeYJavaType sig = SLListOfKeYJavaType.EMPTY_LIST;
	    sig = sig.append(pv.getKeYJavaType());
	    return new MethodReference(
		new ArrayOfExpression(rhs),
		new ProgramElementName(methodName),
		((FieldReference) lhs).getReferencePrefix());
	}
	CopyAssignment ca = new CopyAssignment(lhs, rhs);
	if(lhs instanceof ArrayReference){
	    KeYJavaType ae = 
		serv.getJavaInfo().getKeYJavaTypeByClassName(
		    "java.lang.ArrayIndexOutOfBoundsException");
	    ParameterDeclaration pd = new ParameterDeclaration(
		new Modifier[0],
		new TypeRef(ae),
		new VariableSpecification(
		    new LocationVariable(new ProgramElementName("e"), ae)), 
		false);
	    Branch c = new Catch(pd, new StatementBlock());
	    return new Try(new StatementBlock(ca), new Branch[]{c});
	}else{
	    return ca;
	}
    }

    /**
     * creates the method public static junit.framework.TestSuite suite () ...
     * which is needed for junit test suites.
     */
    private MethodDeclaration createSuiteMethod(){
	ExtList l = new  ExtList();
	l.add(new ProgramElementName("suite"));
	l.add(new Public());
	l.add(new Static());
	l.add(testSuite);
	Statement[] s = new Statement[3];

	SyntacticalProgramVariable suite = 
	    new SyntacticalProgramVariable(new ProgramElementName("suiteVar"),
				testSuite.type);
	s[0] = new LocalVariableDeclaration(testSuite,
					    new VariableSpecification(suite, suite.type));
	Expression[] arg = new Expression[1];
	arg[0] = new MetaClassReference(testTypeRef);
	New cons = new New(arg, testSuite, null);
	s[1] = new CopyAssignment(suite, cons);
	s[2] = new Return(suite);
	StatementBlock mBody = new StatementBlock(s);
	/*The visitor is applied on SyntacticalProgramVariable
	* and the visitor must be implemented such that effectively
	* CreatingASTVisitor.doDefaultAction(x) is invoked where x is
	* the SyntacticalProgramVariable. For this the Visitor interface
	* was be extended, to support actions on IProgramVariable from which
	* SyntacticalProgramVariable is derived.
	*/
	FieldReplaceVisitor frv = new FieldReplaceVisitor(mBody, serv);
	frv.start();
	l.add(frv.result());
	return new MethodDeclaration(l, false);
    }
    

    /**
     * Generates the testcase and writes it to a file.
     * @param code the piece of code that is tested by the generated unittest.
     * @param oracle a term representing the postcondition of 
     *         <code>code</code>. It is used to create a testoracle.
     * @param mgs List of ModelGenerators.
     * @param programVars program variables that have to be declared in the 
     *         method.
     * @param methodName the name of the testmethod created for 
     *         <code>code</code>within the test case.
     */
    public void generateTestSuite(Statement[] code, Term oracle, 
				  List mgs, SetOfProgramVariable programVars,
				  String methodName, PackageReference pr){
	UpdateSimplifier simplifier = new UpdateSimplifier();
	oracle = simplifier.simplify(oracle, serv);
	HashSet processedModels = new HashSet();
	int dm = 0;
	Iterator it = mgs.iterator();
//	ProgramVariable[] pva = null;
	ProgramVariable[] pvaNotDecl = null;
	while(it.hasNext()){
	    ModelGenerator mg = (ModelGenerator) it.next();
	    programVars = programVars.union(mg.getProgramVariables());
	}
	pvaNotDecl = removeDublicates(programVars).toArray();
	it = mgs.iterator();
	ExtList l = new ExtList();
	l.add(suiteMethod);
	int testMCounter = 0;
	while(it.hasNext()){
	    ModelGenerator mg = (ModelGenerator) it.next();
	    Model[] models = mg.createModels();
	    int dublicate = 0;
	    if(models.length-dublicate == 0 && mgs.size()!=1){
		continue;
	    }
	    EquivalenceClass[] eqvArray = mg.getPrimitiveLocationEqvClasses();
	    Expression[][] testLocation = new Expression[eqvArray.length][];
	    Expression[][] testData = 
		new Expression[eqvArray.length][models.length-dublicate];
	    for(int i=0; i<eqvArray.length; i++){
		SetOfTerm locs = eqvArray[i].getLocations();
		testLocation[i] = new Expression[locs.size()];
		int k = 0;
		IteratorOfTerm itt = locs.iterator();
		while(itt.hasNext()){
		    Term testLoc = itt.next();
		    testLocation[i][k++] = translateTerm(testLoc, null, null);
		}
		for(int j=0; j<models.length-dublicate; j++){
		    testData[i][j] = 
			models[j].getValueAsExpression(eqvArray[i]);
		}
	    }
	    l.add(createTestMethod(code, oracle, testLocation, 
				   testData, pvaNotDecl, 
				   methodName+(testMCounter++), l, mg, 
				   eqvArray));
	}

        ClassDeclaration suite = createSuiteClass(l);
	PrettyPrinter pp = new CompilableJavaPP(w, false);
	try{
	    // write the file to disk
	    pp.printClassDeclaration(suite);
	    File dir = new File(directory);
	    if(!dir.exists()){
		dir.mkdirs();
	    }
	    File pcFile = new File(dir, fileName+".java");
	    path = pcFile.getAbsolutePath();
	    FileWriter fw = new FileWriter(pcFile); 
	    BufferedWriter bw = new BufferedWriter(fw); 
	    bw.write(addImports(clean(w.toString()), pr));
	    bw.close(); 
	} catch (IOException ioe) { 
	}	
	exportCodeUnderTest();
    }

    /**
     * Exports the code under test to files and adds get and set methods for
     * each field.
     */
    public void exportCodeUnderTest(){
	final Set<KeYJavaType> kjts = ji.getAllKeYJavaTypes();
	final Iterator<KeYJavaType> it = kjts.iterator();
	while(it.hasNext()){
	    final KeYJavaType kjt = it.next();
	    if((kjt.getJavaType() instanceof ClassDeclaration ||
		kjt.getJavaType() instanceof InterfaceDeclaration) &&
	       ((TypeDeclaration) kjt.getJavaType()).getPositionInfo().
	       getFileName() != null &&
               ((TypeDeclaration) kjt.getJavaType()).getPositionInfo().
               getFileName().indexOf(serv.getProof().getJavaModel().getModelDir())!=-1){

		StringWriter sw = new StringWriter();
		PrettyPrinter pp = new CompilableJavaPP(sw,false);
		try{
		    // write the implementation under test to the testFiles
		    // directory
		    if(kjt.getJavaType() instanceof ClassDeclaration){
			pp.printClassDeclaration((ClassDeclaration) 
						 kjt.getJavaType());
		    }else{
			pp.printInterfaceDeclaration((InterfaceDeclaration) 
						     kjt.getJavaType());
		    }
		    String fn = ((TypeDeclaration) kjt.getJavaType()).
			getPositionInfo().getFileName();

		    String header = getHeader(fn);

		    File dir = new File(directory+
					fn.substring(fn.indexOf(File.separator), fn.lastIndexOf(
							 File.separator)));
		    fn = fn.substring(fn.lastIndexOf(File.separator)+1);
		    if(!dir.exists()){
			dir.mkdirs();
		    }
		    File pcFile = new File(dir, fn);
		    FileWriter fw = new FileWriter(pcFile); 
		    BufferedWriter bw = new BufferedWriter(fw); 
		    bw.write(header);
		    bw.write(clean(sw.toString()));
		    bw.close(); 
		} catch (IOException ioe) { 
		    throw new UnitTestException(ioe);
		}	
	    }
	}
    }

    private String clean(String s){
	while(s.indexOf(";.")!=-1){
	    s = s.substring(0, s.indexOf(";.")) + 
		s.substring(s.indexOf(";.")+1);
	}
	while(s.indexOf(";;")!=-1){
	    s = s.substring(0, s.indexOf(";;")) + 
		s.substring(s.indexOf(";;")+1);
	}
	while(s.indexOf(";[")!=-1){
	    s = s.substring(0, s.indexOf(";[")) + 
		s.substring(s.indexOf(";[")+1);
	}
	while(s.indexOf(";]")!=-1){
	    s = s.substring(0, s.indexOf(";]")) + 
		s.substring(s.indexOf(";]")+1);
	}
	return s;
    }

    /** Returns the header consisting of package and import statements 
     * occuring in the file <code>fileName</code>.
     */
    private String getHeader(String fileName){
	String result = "";
        String lineSeparator = System.getProperty("line.separator");
	BufferedReader reader;
	try{
	    reader = new BufferedReader(new FileReader(fileName));
	    String line;
	    while ((line = reader.readLine()) != null) {
		result += line + lineSeparator;
	    }
	    reader.close();
	}catch(IOException ioe){
	    throw new UnitTestException(ioe);
	}
	int declIndex = result.indexOf("class ");
	if(declIndex == -1){
	    declIndex = result.indexOf("interface ");
	}
	result = result.substring(0, declIndex);
	result = result.substring(0, result.lastIndexOf(";")+1);
	return result+"\n\n";
    }

    public SetOfProgramVariable removeDublicates(SetOfProgramVariable pvs){
	HashSet names = new HashSet();
	IteratorOfProgramVariable it = pvs.iterator();
	SetOfProgramVariable result = SetAsListOfProgramVariable.EMPTY_SET;
	while(it.hasNext()){
	    ProgramVariable pv = it.next();
	    if(names.add(pv.name().toString())){
		result = result.add(pv);
	    }
	}
	return result;
    }

    /** 
     * Returns the path of the file generated by this instance.
     */
    public String getPath(){
	return path;
    }

    private String addImports(String classDec, PackageReference pr){
	String imports = "import junit.framework.*;";
	if(pr!=null){
	    imports += "\nimport "+pr+".*;";
	}
	return imports+"\n\n"+classDec;
    }

    /** Creates a testoracle from the term <code>post</code>.
     * @param post the term used for creating a testoracle.
     * @param buffer a program variable of type StringBuffer.
     * @param children the children of the enclosing class. The MethodDeclarations 
     *       created by this method are added to <code>children</code>.
     */
    public MethodReference getOracle(Term post, 
				     SyntacticalProgramVariable buffer,
				     ExtList children){
	if(oracle==null){
	    post = replaceConstants(post, serv, null);
	    oracle = (MethodReference) getMethodReferenceForFormula(
		post, buffer, children);
	}
	return oracle;
    }

    /**
     * Returns the method reference the term post is translated to and creates
     * also the corresponding method declaration.
     */
    private Expression getMethodReferenceForFormula(Term post, 
                                    SyntacticalProgramVariable buffer,
                                    ExtList children){
	if(post.sort() != Sort.FORMULA){
	    return translateTerm(post, buffer, children);
	}
	if(translatedFormulas.containsKey(post)){
	    return (Expression) translatedFormulas.get(post);
	}
	ExtList args = getArguments(post);
	args.add(buffer);
	LinkedList params = getParameterDeclarations(args);
	Statement[] mBody = buildMethodBodyFromFormula(post, buffer, children);
	MethodDeclaration md = buildMethodDeclaration(mBody, new TypeRef(b),
						      "subformula", params);
	children.add(md);
	MethodReference mr = 
	    new MethodReference(args, new ProgramElementName(md.getName()),
				testTypeRef);
	translatedFormulas.put(post, mr);
	return mr;
    }

    /**
     * Creates the method body for the method the term post is translated to.
     */
    private Statement[] buildMethodBodyFromFormula(Term post, 
                                                   SyntacticalProgramVariable buffer,
                                                   ExtList children){
	Statement[] s = new Statement[4];
	ProgramVariable result = 
	    new LocationVariable(new ProgramElementName(resultName), b);
	s[0] = new LocalVariableDeclaration(new TypeRef(b), 
					    new VariableSpecification(result));
	Expression f = translateFormula(post, buffer, children);
	s[1] = new CopyAssignment(result, f);
	Plus str = new Plus(new StringLiteral("\\neval("+post+") = "), result);
	s[2] = new MethodReference(new ArrayOfExpression(str), 
				   new ProgramElementName("append"), 
				   buffer);
	s[3] = new Return(result);
	return s;
    }

    /**
     * Translates a term to a java expression. 
     */
    private Expression translateTerm(Term t, 
                                     SyntacticalProgramVariable buffer,
                                     ExtList children){
	Expression result = null;
	if (t.op() instanceof ProgramInLogic) {
	    final ExtList tchildren = new ExtList();
	    for (int i=0; i<t.arity(); i++) {
		tchildren.add(translateTerm(t.sub(i), buffer, children));
	    }
	    return ((ProgramInLogic)t.op()).convertToProgram(t, tchildren);
	}else if(t.op() == Op.IF_THEN_ELSE){
	    ExtList l = new ExtList();
	    l.add(getMethodReferenceForFormula(t.sub(0), 
					       buffer, children));
	    l.add(translateTerm(t.sub(1), buffer, children));
	    l.add(translateTerm(t.sub(2), buffer, children));
	    result = new Conditional(l); 
	    result = new ParenthesizedExpression(result);
	}else if (t.op() instanceof Function) {
	    String name = t.op().name().toString().intern();
	    if (name.equals("add") || name.equals("jadd") ||
		name.equals("addJint")) {
		result = new Plus(translateTerm(t.sub(0), buffer, 
						children), 
				  translateTerm(t.sub(1), buffer, 
						children));
	    } else if (name.equals("sub") || name.equals("jsub") || 
		       name.equals("subJint")) {
		result = new Minus(translateTerm(t.sub(0), buffer, children),
				   translateTerm(t.sub(1), buffer, children));
	    } else if (name.equals("neg") || name.equals("jneg")
		       || name.equals("negJint") || name.equals("neglit")) {
		result = new Negative(translateTerm(t.sub(0), 
						    buffer, children));
	    } else if (name.equals("mul") || name.equals("jmul") 
		       || name.equals("mulJint")) {
		result = new Times(translateTerm(t.sub(0), 
						 buffer, children),
				   translateTerm(t.sub(1), buffer, 
						 children));
	    } else if (name.equals("div") || name.equals("jdiv") 
		       || name.equals("divJint")) {
		result = new Divide(translateTerm(t.sub(0), 
						  buffer, children), 
				    translateTerm(t.sub(1), 
						  buffer, children));
	    } else if (name.equals("mod") || name.equals("jmod") 
		       || name.equals("modJint")) {
		result = new Modulo(translateTerm(t.sub(0), 
						  buffer, children), 
				    translateTerm(t.sub(1), buffer, 
						  children));
	    } else if (name.equals("Z")) {
		result = translateTerm(t.sub(0), buffer, children);
	    } else if(t.op() instanceof CastFunctionSymbol){
	        result = translateTerm(t.sub(0), buffer, children);
	    }
	    if(result!=null){
		result = new ParenthesizedExpression(result);
	    }
	}
	if(result==null){
                try {
                    result = convertToProgramElement(t);
                } catch (Exception e) {
                    throw new RuntimeException(
                            "The exception \n"
                                    + e.getMessage()
                                    + "\nwas thrown. It is possible, that this is caused by the wrong default behavior in translateTerm !");
                }

            }
	return result;
    }

    /**
     * Translates a formula to a java expression, i.e. an oracle for the 
     * is created
     * @param children the children of the enclosing class. The method 
     *         declarations created by this method are added to <code>
     *         children</code>.
     */
    private Expression translateFormula(Term post, 
					SyntacticalProgramVariable buffer,
					ExtList children){
	ExtList l = new ExtList();
	if(post.sort() != Sort.FORMULA){
	    return translateTerm(post, buffer, children);
	}else if(post.op() == Op.TRUE){
	    return BooleanLiteral.TRUE;
	}else if(post.op() == Op.FALSE){
	    return BooleanLiteral.FALSE;
	}else if(post.op() == Op.NOT){
	    l.add(new ParenthesizedExpression(
		      translateFormula(post.sub(0), buffer, children)));
	    return new LogicalNot(l);
	}else if(post.op() == Op.AND){
	    return new LogicalAnd(
		getMethodReferenceForFormula(post.sub(0), buffer, children),
		getMethodReferenceForFormula(post.sub(1), buffer, children));
	}else if(post.op() == Op.OR){
	    return new LogicalOr(
		getMethodReferenceForFormula(post.sub(0), buffer, children),
		getMethodReferenceForFormula(post.sub(1), buffer, children));
	}else if(post.op() == Op.IMP){
	    l.add(getMethodReferenceForFormula(post.sub(0), buffer, children));
	    return new LogicalOr(
		new LogicalNot(l),
		getMethodReferenceForFormula(post.sub(1), buffer, children));
	}else if(post.op() instanceof Equality){
	    l.add(getMethodReferenceForFormula(post.sub(0), buffer, children));
	    l.add(getMethodReferenceForFormula(post.sub(1), buffer, children));
	    Equals eq = new Equals(l);
	    return eq;
	}else if(post.op() == Op.IF_THEN_ELSE){
	    l.add(getMethodReferenceForFormula(post.sub(0), buffer, children));
	    l.add(getMethodReferenceForFormula(post.sub(1), buffer, children));
	    l.add(getMethodReferenceForFormula(post.sub(2), buffer, children));
	    return new Conditional(l); 
	}else if(post.op() == Op.ALL){
	    return translateQuantifiedTerm(true, post, buffer, children);
	}else if(post.op() == Op.EX){
	    return translateQuantifiedTerm(false, post, buffer, children);
	}else if(post.op().name().toString().equals("lt")){
	    return new LessThan(translateTerm(post.sub(0), buffer, children), 
				translateTerm(post.sub(1), buffer, children));
	}else if(post.op().name().toString().equals("gt")){
	    l.add(translateTerm(post.sub(0), buffer, children));
	    l.add(translateTerm(post.sub(1), buffer, children));
	    return new GreaterThan(l);
	}else if(post.op().name().toString().equals("geq")){
	    l.add(translateTerm(post.sub(0), buffer, children));
	    l.add(translateTerm(post.sub(1), buffer, children));
	    return new GreaterOrEquals(l);
	}else if(post.op().name().toString().equals("leq")){
	    return new LessOrEquals(translateTerm(post.sub(0), 
						  buffer, children),
				       translateTerm(post.sub(1), 
						     buffer, children));
	}
	throw new NotTranslatableException("Test oracle could not be generated");
    }

    /**
     * Builds a method declaration with the provided name and type.
     * Field references o.a occuring in the method body are replaced
     * by methodcalls o._a().
     */
    private MethodDeclaration buildMethodDeclaration(Statement[] body, 
						     TypeRef type,
						     String name,
						     LinkedList params){
	ExtList l = new  ExtList();
	l.add(new ProgramElementName(name+(mcounter++)));
	l.add(new Private());
	l.add(new Static());
	l.addAll(params);
	l.add(type);
	StatementBlock mBody = new StatementBlock(body);
	FieldReplaceVisitor frv = new FieldReplaceVisitor(mBody, serv);
	frv.start();
	l.add(frv.result());
	MethodDeclaration md = new MethodDeclaration(l, false);
	return md;
    }

    /**
     * Creates an oracle for a quantified formula, which is only possible for 
     * some classes of quantified formulas. If <code>t</code> doesn't belong
     * to one of these classes a NotTranslatableException is thrown.
     */
    private Expression translateQuantifiedTerm(boolean all,
					       Term t, 
					       SyntacticalProgramVariable buffer,
					       ExtList children){
	de.uka.ilkd.key.logic.op.Operator junctor;
	Expression resInit;
	if(all){
	    junctor = Op.IMP;
	    resInit = BooleanLiteral.TRUE;
	}else{
	    junctor = Op.AND;
	    resInit = BooleanLiteral.FALSE;	    
	}
//	if(true ) return BooleanLiteral.TRUE;
	Statement[] body = new Statement[4];
	Expression[] bounds = new Expression[]{null, null, null, null};
	LogicVariable lv = 
	    (LogicVariable) t.varsBoundHere(0).lastQuantifiableVariable();
	if(t.varsBoundHere(0).size() > 1 || !(lv.sort() == intType.getSort() ||
					      lv.sort().toString().
					      equals("jint"))){
	    throw new NotTranslatableException("quantified Term "+t);
	}
	ProgramVariable result = 
	    new LocationVariable(new ProgramElementName("result"), b);
	body[0] = new LocalVariableDeclaration(
	    new TypeRef(b), new VariableSpecification(result, 
						      resInit,
						      b.getJavaType())); 
	KeYJavaType lvType = intType;
	ProgramVariable pv = 
	    new LocationVariable(new ProgramElementName(
				    "_"+lv.name()+(counter++)), lvType);
	Term sub0 = replaceLogicVariable(t.sub(0), lv, pv);
	if(sub0.op() == junctor && sub0.sub(0).op() == Op.AND){
	    Term range = sub0.sub(0);
	    getBound(range.sub(0), bounds, pv, buffer, children);
	    getBound(range.sub(1), bounds, pv, buffer, children);
	}else if(sub0.op() == junctor && sub0.sub(1).op() == junctor){
	    getBound(sub0.sub(0), bounds, pv, buffer, children);
	    getBound(sub0.sub(1).sub(0), bounds, pv, buffer, children);
	}else{
	    throw new NotTranslatableException("quantified Term "+t);
	}
	
	Statement loopBody = new CopyAssignment(
	    result, all ? 
	    (Expression) new LogicalAnd(result, getMethodReferenceForFormula(
					    sub0.sub(1), buffer, children))
	    :
	    (Expression) new LogicalOr(result, getMethodReferenceForFormula(
					   sub0.sub(1), buffer, children))
	    );
	VariableSpecification vs = new VariableSpecification(
	    pv, bounds[0]!=null ? bounds[0] : new Plus(bounds[1], 
						       new IntLiteral(1)), 
	    intType.getJavaType());
	LocalVariableDeclaration init = 
	    new LocalVariableDeclaration(new TypeRef(intType), vs);
	Expression guard = bounds[2]==null ? 
	    (Expression) new LessThan(pv, bounds[3]) : 
	    (Expression) new LessOrEquals(pv, bounds[2]);
	Expression update = new PostIncrement(pv);
	body[1] = new For(new LoopInitializer[]{init}, guard, 
			  new Expression[]{update}, 
			  new StatementBlock(loopBody));
	Plus str = new Plus(new StringLiteral("\\neval("+t+") = "), result);
	body[2] = new MethodReference(new ArrayOfExpression(str), 
				      new ProgramElementName("append"), 
				      buffer);
	body[3] = new Return(result);
	
	ExtList args = getArguments(t);
	args.add(buffer);
	LinkedList params = getParameterDeclarations(args);
	
	MethodDeclaration md = buildMethodDeclaration(body,
						      new TypeRef(b), 
						      "quantifierTerm", 
						      params);
	children.add(md);
	return new MethodReference(args, new ProgramElementName(md.getName()),
				   testTypeRef);
    }

    /**
     * Returns the location variables occuring in t that are no attributes.
     */
    private ExtList getArguments(Term t){
	SetOfProgramVariable programVars = 
	    SetAsListOfProgramVariable.EMPTY_SET;
	TermProgramVariableCollector pvColl = 
	    new TermProgramVariableCollector(serv);
	t.execPreOrder(pvColl);
	Iterator itp = pvColl.result().iterator();
	while(itp.hasNext()){
	    ProgramVariable v = (ProgramVariable) itp.next();
	    if(!v.isMember()){
		programVars = programVars.add(v);
	    }
	}
	programVars = removeDublicates(programVars);
	IteratorOfProgramVariable it = programVars.iterator();
	ExtList args = new ExtList();
	while(it.hasNext()){
	    args.add(it.next());
	}
	return args;
    }

    private LinkedList getParameterDeclarations(ExtList l){
	LinkedList params = new LinkedList();
	Iterator it = l.iterator();
	while(it.hasNext()){
	            IProgramVariable arg = (IProgramVariable) it.next();
            // Depending wether it's a ProgramVariable or
            // SyntacticalProgramVariable
            // the type has to be obtained in two different ways.
            if (arg instanceof ProgramVariable) {// chris
                KeYJavaType kjt = arg.getKeYJavaType();
                params.add(new ParameterDeclaration(
                        new Modifier[0],
                        new TypeRef(kjt),
                        new VariableSpecification(arg), 
                        false));
            } else if (arg instanceof SyntacticalProgramVariable) {
                SyntacticalProgramVariable syntArg = (SyntacticalProgramVariable) arg;
                params.add(new ParameterDeclaration(
                        new Modifier[0],
                        new SyntacticalTypeRef(syntArg.type),
                        new VariableSpecification(arg, syntArg.type), 
                        false));
            } else {
                throw new RuntimeException(
                        "Unexpected case: arg is instance of:"+arg);
            }
	}
	return params;
    }

    /**
     * Trys to extract bounds for the quantified integer variable.
     */
    private void getBound(Term t, Expression[] bounds, ProgramVariable pv, 
			  SyntacticalProgramVariable buffer, ExtList children){
	int ex=0, less=1;
	if((t.op().name().toString().equals("!") || 
	    t.op().name().toString().equals("not")) && 
	   t.sub(0).op().name().toString().equals("lt")){
	    t = t.sub(0);
	    less = 0;
	}else if(t.op().name().toString().equals("lt")){
	    ex = 1;
	}else if(t.op().name().toString().equals("leq")){
	}else if(t.op().name().toString().equals("geq")){
	    less = 0;
	}else if(t.op().name().toString().equals("gt")){
	    ex = 1;
	    less = 0;
	}else{
	    throw new NotTranslatableException("bound "+t+
					       " for quantified variable");
	}
	if(t.sub(0).op() == pv){
	    bounds[2*less+ex] = translateTerm(t.sub(1), buffer, children);
	}else if(t.sub(1).op() == pv){
	    bounds[2-2*less+ex] = translateTerm(t.sub(0), buffer, children);
	}else{
	    throw new NotTranslatableException("bound "+t+
					       " for quantified variable");
	}
    }

    /**
     * replaces all occurences of lv in t with pv.
     */
    private Term replaceLogicVariable(Term t, LogicVariable lv, 
				      ProgramVariable pv){
	TermFactory tf = TermFactory.DEFAULT;
	Term result = null;
	if(t.op() == lv){
	    return tf.createVariableTerm(pv);
	}else {
	    Term subTerms[] = new Term[t.arity()];
            ArrayOfQuantifiableVariable[] quantVars = 
		new ArrayOfQuantifiableVariable[t.arity()];
	    for ( int i = 0; i<t.arity(); i++ ) {
		quantVars[i] = t.varsBoundHere(i);
		subTerms[i] = replaceLogicVariable(t.sub(i), lv, pv);
	    }
            JavaBlock jb = t.javaBlock();
	    result = tf.createTerm(t.op(), subTerms, quantVars, jb);
	}
	return result;
    }

    /**
     * Converts <code>t</code> to a ProgramElement. If <code>t</code> is
     * a (skolem)constant, a new identically named ProgramVariable of the
     * same sort is returned.
     */
    public Expression convertToProgramElement(Term t){
	t = replaceConstants(t, serv, null);
	return serv.getTypeConverter().convertToProgramElement(t);
    }

    /**
     * Replaces rigid constants by program variables.
     */
    protected static Term replaceConstants(Term t, Services serv, 
					   Namespace newPVs){
	TermFactory tf = TermFactory.DEFAULT;
	Term result = null;
	if(t.op() instanceof RigidFunction && t.arity()==0 &&
	   !"#".equals(t.op().name().toString()) &&
	   !"TRUE".equals(t.op().name().toString()) &&
	   !"FALSE".equals(t.op().name().toString()) &&
	   t.op() != Op.NULL){
	    KeYJavaType kjt = 
		serv.getJavaInfo().getKeYJavaType(t.sort().toString());
	    if(t.sort().toString().startsWith("jint")){
		kjt = serv.getJavaInfo().getKeYJavaType(
		    t.sort().toString().substring(1));
	    }
	    ProgramVariable pv = new LocationVariable(
		new ProgramElementName(t.op().name().toString()), kjt);
	    if(newPVs != null){
		newPVs.add(pv);
	    }
	    return tf.createVariableTerm(pv);
	}else if(t.op() instanceof ProgramVariable){
	    if(newPVs != null && 
	       !((ProgramVariable) t.op()).isStatic()){	    
		newPVs.add((ProgramVariable) t.op());
	    }
	    return t;
	}else{
	    Term subTerms[] = new Term[t.arity()];
            ArrayOfQuantifiableVariable[] quantVars = 
		new ArrayOfQuantifiableVariable[t.arity()];
	    for ( int i = 0; i<t.arity(); i++ ) {
		quantVars[i] = t.varsBoundHere(i);
		subTerms[i] = replaceConstants(t.sub(i), serv, newPVs);
	    }
            JavaBlock jb = t.javaBlock();
	    result = tf.createTerm(t.op(), subTerms, quantVars, jb);
	}
	return result;
    }

}
