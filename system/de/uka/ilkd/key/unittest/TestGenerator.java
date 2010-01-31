package de.uka.ilkd.key.unittest;

import java.io.*;
import java.util.*;

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.declaration.modifier.Private;
import de.uka.ilkd.key.java.declaration.modifier.Public;
import de.uka.ilkd.key.java.declaration.modifier.Static;
import de.uka.ilkd.key.java.expression.ArrayInitializer;
import de.uka.ilkd.key.java.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.expression.literal.StringLiteral;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.If;
import de.uka.ilkd.key.java.statement.Return;
import de.uka.ilkd.key.java.statement.Then;
import de.uka.ilkd.key.java.visitor.FieldReplaceVisitor;
import de.uka.ilkd.key.java.visitor.IndexReplaceVisitor;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.ArraySortImpl;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.ProofSaver;
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.rule.soundness.TermProgramVariableCollector;
import de.uka.ilkd.key.unittest.AssGenFac.AssignmentGenerator;
import de.uka.ilkd.key.unittest.ppAndJavaASTExtension.*;
import de.uka.ilkd.key.unittest.testing.DataStorage;
import de.uka.ilkd.key.util.ExtList;
import de.uka.ilkd.key.visualdebugger.VisualDebugger;

/**
 * @author mbender
 *
 */
/**
 * @author mbender
 *
 */
/**
 * @author mbender
 *
 */
public abstract class TestGenerator {

    protected static final String RESULT_NAME = "_oracleResult";

    protected final Services serv;

    private final String fileName;

    protected final String directory;

    protected final boolean testing;

    private final AssignmentGenerator ag;

    // It should be possible to get rid of JavaInfo entirely if all KeYJavaTypes
    // are "replaced" by SyntacticalTypeRefs. This would make the class more
    // independent from the type system known by in JavaInfo.
    protected final JavaInfo ji;

    protected final String modDir;

    protected final SyntacticalTypeRef testTypeRef;

    protected final KeYJavaType booleanType;

    protected final KeYJavaType intType;

    private int mcounter = 0;

    private final HashMap<Term, Expression> translatedFormulas;

    private DataStorage data;

    public Thread modelGenThread = null;

    /** Seconds to wait for modelGeneration for each node. -1 = infinitely. */
    public static volatile int modelCreationTimeout = 100;

    public final TestGeneratorGUIInterface gui;

    /**
     * creates a TestGenerator instance for the given compilation unit
     * 
     * @param serv
     *            the Services
     * @param fileName
     *            the name of the unittest file this TestGenerator creates.
     * @param directory
     *            the directory of the unittest file this TestGenerator creates.
     * @param testing
     *            A boolean flag that indicates if the class was called during
     *            from the runTest regression testing script.
     * @param ag
     *            the AssignmentGenerator to use.
     * @param gui
     *            is allowed to be null. Otherwise the gui interface is used to
     *            display test generation progress to the user.
     */
    @SuppressWarnings("unchecked")
    protected TestGenerator(final Services serv, final String fileName,
	    final String directory, final boolean testing,
	    final AssignmentGenerator ag, final TestGeneratorGUIInterface gui) {
	this.serv = serv;
	this.fileName = fileName;
	if (directory != null) {
	    this.directory = directory;
	} else {
	    this.directory = System.getProperty("user.home") + File.separator
		    + "testFiles";
	}
	this.testing = testing;
	this.ag = ag;

	ji = serv.getJavaInfo();

	modDir = serv.getProof().getJavaModel().getModelDir();

	translatedFormulas = new HashMap<Term, Expression>();

	final ExtList l = new ExtList();
	l.add(new ProgramElementName(fileName));

	testTypeRef = new SyntacticalTypeRef(new ClassDeclaration(l,
	        new ProgramElementName(fileName), false));

	// You can create a SyntacticalTypeRef for BooleanType as well if
	// JavaInfo doesn't provide it (as it should be in a clean
	// typesystem for JavaCard).
	booleanType = ji.getTypeByName("boolean");
	// You can create a SyntacticalTypeRef for Integer type as well if
	// JavaInfo doesn't provide it (as it should be in a clean
	// typesystem for JavaCard).
	intType = ji.getTypeByName("int");

	this.gui = gui;
    }

    /**
     * Generates the testcase and writes it to a file. It uses background
     * threads that access the field TestGenerator.modelCreationTimeout.
     * 
     * @param code
     *            the piece of code that is tested by the generated unittest.
     * @param oracle
     *            a term representing the postcondition of <code>code</code> .
     *            It is used to create a testoracle.
     * @param mgs
     *            List of ModelGenerators.
     * @param programVars
     *            program variables that have to be declared in the method.
     * @param methodName
     *            the name of the testmethod created for <code>code</code>
     *            within the test case.
     * @param pr
     *            the reference to the package.
     * @return The string that show the path of the generated file
     */
    @SuppressWarnings("unchecked")
    synchronized public String generateTestSuite(final Statement[] code,
	    Term oracle, final List<ModelGenerator> mgs,
	    ImmutableSet<ProgramVariable> programVars, final String methodName,
	    final PackageReference pr) {
	oracle = new UpdateSimplifier().simplify(oracle, serv);
	for (final ModelGenerator mg : mgs) {
	    programVars = programVars.union(mg.getProgramVariables());
	}
	final ImmutableSet<ProgramVariable> reducedPVSet = removeDublicates(programVars);
	data.setPvs2(reducedPVSet);
	ExtList l = new ExtList();
	l.add(createSuiteMethod());
	// Add methods to compute min or max element of an array
	l.add(createMinMaxMethod(true));
	l.add(createMinMaxMethod(false));
	// collect testmethods for use when creating the main() method. Also
	// used to increment a counter of the test methods for automatic
	// unique naming.
	final Vector<MethodDeclaration> testMethods = new Vector<MethodDeclaration>();
	int count = 0;
	final int totalCount = mgs.size();
	generateTestSuite_progressNotification0(totalCount);
	while (mgs.size() > 0) {
	    // modelGenerators are removed from the list (and hopefully
	    // destroyed) in order to save memory.
	    final ModelGenerator mg = mgs.get(0);
	    Model[] models = null;
	    MethodDeclaration methDec = null;
	    count++;
	    try {

		generateTestSuite_progressNotification1(count, totalCount, mg);
		ModelGeneratorRunnable modelGeneration = null;
		if (!testing) {
		    // Model generation. The threads implement a timeout-feature
		    // for model generation.
		    modelGeneration = new ModelGeneratorRunnable(mg);
		    models = modelGeneration.createModels();
		} else {
		    // The following call does not run another thread
		    models = mg.createModels();
		}

		// Read model
		final boolean createModelsFailed = models == null || (models.length == 0);
		generateTestSuite_progressNotification2(count, totalCount, mg, models, !createModelsFailed,
		        (modelGeneration != null && modelGeneration.wasInterrupted()));
		if (createModelsFailed) {
		    // This ModelGenerator has been used in this iteration and
		    // is not needed anymore
		    mgs.remove(0);
		    continue;
		}
		final EquivalenceClass[] intOrBoolEqvArray = mg.getPrimitiveLocationEqvClasses();
		final Expression[][] testLocation = new Expression[intOrBoolEqvArray.length][];
		final Expression[][] testData = new Expression[intOrBoolEqvArray.length][models.length];
		for (int i = 0; i < intOrBoolEqvArray.length; i++) {
		    final ImmutableSet<Term> locs = intOrBoolEqvArray[i].getLocations();
		    testLocation[i] = new Expression[locs.size()];
		    int k = 0;
		    for (final Term testLoc : locs) {
			testLocation[i][k++] = translateTerm(testLoc, null, null);
		    }
		    for (int j = 0; j < models.length; j++) {
			testData[i][j] = models[j].getValueAsExpression(intOrBoolEqvArray[i]);
			if (testData[i][j] == null) {
			    // Emergency solution.
			    // Was earlier in Model.getValueAsExpressions()
			    testData[i][j] = new IntLiteral(15);
			    generateTestSuite_progressNotification2b(count, totalCount, mg, intOrBoolEqvArray[i]);
			}
		    }
		}
		// mbender: collect data for KeY junit tests (see
		// TestTestGenerator,TestHelper)
		data.addTestDat(testData);
		data.addTestLoc(testLocation);
		methDec = createTestMethod(code, oracle, testLocation,
		        testData, reducedPVSet, methodName
		                + (testMethods.size()), l, mg,
		        intOrBoolEqvArray);
		l.add(methDec);
		testMethods.add(methDec);
		generateTestSuite_progressNotification3(count, totalCount, mg,
		        models, methDec);
	    } catch (final Exception e) {
		generateTestSuite_progressNotification4(count, totalCount, e,
		        mg, models, methDec);
	    }
	    // This ModelGenerator has been used in this iteration and is not
	    // needed anymore
	    mgs.remove(0);
	}

	// Create main() method. Required for the KeYGenU Tool chain.
	l = createMain(l, testMethods);

	final ClassDeclaration suite = createSuiteClass(l);

	String path = "";

	if (!testing) {
	    final StringWriter w = new StringWriter();
	    final PrettyPrinter pp;
	    if (TestGenFac.testGenMode == TestGenFac.TG_USE_SETGET) {
		pp = new CompilableJavaCardPP(w, false);
	    } else if (TestGenFac.testGenMode == TestGenFac.TG_USE_REFL) {
		pp = new CompilableJavaPP(w, false);
	    } else {
		pp = null;
	    }
	    try {
		// write the file to disk
		pp.printClassDeclaration(suite);
		final File dir = new File(directory + modDir);
		if (!dir.exists()) {
		    dir.mkdirs();
		}
		final File pcFile = new File(dir, fileName + ".java");
		path = pcFile.getAbsolutePath();
		final FileWriter fw = new FileWriter(pcFile);
		final BufferedWriter bw = new BufferedWriter(fw);
		bw.write(addImports(clean(w.toString()), pr));
		bw.close();
	    } catch (final IOException ioe) {
	    }
	    exportCodeUnderTest();
	}
	return path;
    }

    /**
     * When generateTestSuite() is executed on a separate thread, then this
     * notification method is called in order to report the progress of
     * computation to other threads.
     */
    private void generateTestSuite_progressNotification0(final int totalCount) {
	if (gui != null) {
	    gui.generateTestSuite_progressNotification0(totalCount);
	}
    }

    /**
     * When generateTestSuite() is executed on a separate thread, then this
     * notification method is called in order to report the progress of
     * computation to other threads.
     */
    private void generateTestSuite_progressNotification1(final int count,
	    final int totalCount, final ModelGenerator refMG) {
	if (gui != null) {
	    gui.generateTestSuite_progressNotification1(count, totalCount,
		    refMG);
	}
    }

    /**
     * When generateTestSuite() is executed on a separate thread, then this
     * notification method is called in order to report the progress of
     * computation to other threads.
     */
    private void generateTestSuite_progressNotification2(final int count,
	    final int totalCount, final ModelGenerator refMG,
	    final Model[] models, final boolean createModelsSuccess,
	    final boolean terminated) {
	// TODO This call seems to cause some trouble, therefore skipped
	// if (gui != null) {
	// gui.generateTestSuite_progressNotification2(count, totalCount, refMG,
	// models, createModelsSuccess, terminated);
	// }
	return;
    }

    /**
     * When generateTestSuite() is executed on a separate thread, then this
     * notification method is called in order to report the progress of
     * computation to other threads.
     */
    private void generateTestSuite_progressNotification2b(final int count,
	    final int totalCount, final ModelGenerator refMG,
	    final EquivalenceClass ec) {
	if (gui != null) {
	    gui.generateTestSuite_progressNotification2b(count, totalCount,
		    refMG, ec);
	} else {
	    System.err.println("No test data available for equivalence class:"
		    + ec.toString());
	}
    }

    /**
     * When generateTestSuite() is executed on a separate thread, then this
     * notification method is called in order to report the progress of
     * computation to other threads.
     */
    private void generateTestSuite_progressNotification3(final int count,
	    final int totalCount, final ModelGenerator refMG,
	    final Model[] models, final MethodDeclaration mDecl) {
	if (gui != null) {
	    gui.generateTestSuite_progressNotification3(count, totalCount,
		    refMG, models, mDecl);
	}
    }

    /**
     * When generateTestSuite() is executed on a separate thread, then this
     * notification method is called in order to report the progress of
     * computation to other threads. This method is overwritten by
     * TestGeneratorGUIInterface
     */
    private void generateTestSuite_progressNotification4(final int count,
	    final int totalCount, final Exception e,
	    final ModelGenerator refMG, final Model[] models,
	    final MethodDeclaration mDecl) {
	if (gui != null) {
	    gui.generateTestSuite_progressNotification4(count, totalCount, e,
		    refMG, models, mDecl);
	} 
    }

    /**
     * Removes the dublicates from e given set of programVariables and returns
     * the new set.
     * 
     * @param pvs
     *            the set of ProgramVariables
     * @return the set of ProgramVariables that contains no dublicate elements
     */
    private ImmutableSet<ProgramVariable> removeDublicates(
	    final ImmutableSet<ProgramVariable> pvs) {
	final HashSet<String> names = new HashSet<String>();
	ImmutableSet<ProgramVariable> result = DefaultImmutableSet.<ProgramVariable> nil();
	for (final ProgramVariable pv : pvs) {
	    if (names.add(pv.name().toString())) {
		result = result.add(pv);
	    }
	}
	return result;
    }

    /**
     * creates the method public static junit.framework.TestSuite suite () ...
     * which is needed for junit test suites.
     * 
     * @return The MethodDecalaration
     */
    @SuppressWarnings("unchecked")
    private MethodDeclaration createSuiteMethod() {
	final ExtList l = new ExtList();
	l.add(new ProgramElementName("suite"));
	l.add(new Public());
	l.add(new Static());
	final SyntacticalTypeRef testSuite = new SyntacticalTypeRef(
	        new ClassDeclaration(new ProgramElementName("TestSuite"),
	                new ProgramElementName("junit.framework.TestSuite")));
	l.add(testSuite);
	final Statement[] s = new Statement[3];

	final SyntacticalProgramVariable suite = new SyntacticalProgramVariable(
	        new ProgramElementName("suiteVar"), testSuite.type);
	s[0] = new LocalVariableDeclaration(testSuite,
	        new VariableSpecification(suite, suite.type));
	final Expression[] arg = new Expression[1];
	arg[0] = new MetaClassReference(testTypeRef);
	final New cons = new New(arg, testSuite, null);
	s[1] = new CopyAssignment(suite, cons);
	s[2] = new Return(suite);

	l.add(replace(new StatementBlock(s)));
	return new MethodDeclaration(l, false);
    }

    protected ProgramElement replace(final StatementBlock mBody) {
	/*
	 * The visitor is applied on SyntacticalProgramVariable and the visitor
	 * must be implemented such that effectively
	 * CreatingASTVisitor.doDefaultAction(x) is invoked where x is the
	 * SyntacticalProgramVariable. For this the Visitor interface was be
	 * extended, to support actions on IProgramVariable from which
	 * SyntacticalProgramVariable is derived.
	 */
	final FieldReplaceVisitor frv = new FieldReplaceVisitor(mBody, serv);
	frv.start();
	return frv.result();

    }

    /**
     * Creates the class declaration of the unit test that should be exported to
     * a file.
     * 
     * @param l
     * @return The class Declaration
     */
    @SuppressWarnings("unchecked")
    private ClassDeclaration createSuiteClass(final ExtList l) {
	l.add(new Public());
	final SyntacticalTypeRef testCase = new SyntacticalTypeRef(
	        new ClassDeclaration(new ProgramElementName("TestCase"),
	                new ProgramElementName("junit.framework.TestCase")));
	l.add(new Extends(testCase));
	l.add(new ProgramElementName(fileName));
	return new ClassDeclaration(l, new ProgramElementName(fileName), false);
    }

    private KeYJavaType getArrayTypeAndEnsureExistence(
	    final KeYJavaType baseType, final int dim) {
	final Sort as = ArraySortImpl.getArraySortForDim(baseType.getSort(),
	        dim, ji.getJavaLangObjectAsSort(),
	        ji.getJavaLangCloneableAsSort(),
	        ji.getJavaIoSerializableAsSort());
	final KeYJavaType kjt = ji.getKeYJavaType(as);
	if (kjt == null || baseType.getSort().toString().equals("int")) {
	    final JavaBlock jb = ji.readJavaBlock("{" + as + " v;}");
	    return ((VariableDeclaration) ((StatementBlock) jb.program()).getChildAt(0)).getTypeReference().getKeYJavaType();
	}
	return kjt;
    }

    protected KeYJavaType getBaseType(final KeYJavaType arrayType) {
	return ((ArrayType) arrayType.getJavaType()).getBaseType().getKeYJavaType();
    }

    /**
     * Creates a method of the form: public void <name>(){ &lt pv-decls for
     * v0,...,vl &gt; testData0 = {d_00,...,d_0k}; ... testDataj =
     * {d_j0,...,d_jk}; for(int i=0; i<testData0.length; i++){ ... l0 =
     * testData0[i]; ... lj = testDataj[i]; <code>
     *        java.lang.StringBuffer buffer;
     *        buffer = new java.lang.StringBuffer ();
     * 	      boolean result = testOracle(v0,..., vl, buffer);
     *        assertTrue (&lt String &gt, result);
     *    }
     *  }
     *  Where &lt String &gt contains the assignments of l0,...,lj in this
     *  iteration and the results the oracles for the subformulas of post
 *  have provided so far.
     * 
     */
    @SuppressWarnings("unchecked")
    private MethodDeclaration createTestMethod(final Statement code[],
	    final Term post, final Expression[][] testLocation,
	    final Expression[][] testData,
	    final ImmutableSet<ProgramVariable> reducedPVSet,
	    final String name, final ExtList children, final ModelGenerator mg,
	    final EquivalenceClass[] testLocEqvs) {
	// declare and initialize program variables
	ImmutableList<Statement> s = declareAndInitProgVars(reducedPVSet);

	final boolean singleTuple = singleTuple(testData);

	// put test data in array
	final ProgramVariable[] testArray = initTestDataArr(testData.length,
	        singleTuple, testLocEqvs);

	// create Statements
	s = appendStatements(testData.length, singleTuple, testLocEqvs,
	        testArray, s, testData);

	final ExtList l = new ExtList();
	l.add(new ProgramElementName(name));
	l.add(new Public());

	final ProgramVariable partCounter = new LocationVariable(
	        new ProgramElementName("testDataCounter"), intType);

	// initialization of arrays and creation of test data assignments
	final HashMap<String, NewArray> array2Cons = new HashMap<String, NewArray>();
	ImmutableList<Statement> testDataAssignments = ImmutableSLList.<Statement> nil();
	for (int i = 0; i < testData.length; i++) {
	    for (int k = 0; k < testLocation[i].length; k++) {
		final Expression testDat = singleTuple ? testArray[i]
		        : new ArrayReference(testArray[i],
		                new Expression[] { partCounter });
		if (testLocation[i][k] instanceof FieldReference
		        && ((FieldReference) testLocation[i][k])
		                .getProgramVariable().name().toString().equals(
		                        "length")) {
		    // Generate an array constructor call respecting the correct
		    // size/length of the array.
		    // The size of the array is given by the test data
		    // "testDat".
		    final KeYJavaType arrType = ((Expression) ((FieldReference) testLocation[i][k])
			    .getReferencePrefix()).getKeYJavaType(serv, null);
		    if (arrType.getSort() instanceof ArraySort) {
			final NewArray arrayConstructor = new NewArray(
			        new Expression[] { testDat }, new TypeRef(
			                getBaseType(arrType)), arrType, null, 0);
			array2Cons.put(((FieldReference) testLocation[i][k])
			        .getReferencePrefix().toString(),
			        arrayConstructor);
			continue;
		    }
		}
		final IndexReplaceVisitor irv = new IndexReplaceVisitor(
		        testLocation[i][k], testLocation, singleTuple,
		        partCounter, testArray, serv);
		irv.start();
		irv.result();
		testDataAssignments = testDataAssignments.append(ag
		        .assignmentOrSet((Expression) irv.result(), testDat,
		                serv));
	    }
	}

	// initialization of other object references
	final EquivalenceClass[] nonPrim = mg
	        .getNonPrimitiveLocationEqvClasses();
	final HashMap<Expression, Expression> loc2constrCall = new HashMap<Expression, Expression>();
	final LinkedList<Expression> locationsOrdered = new LinkedList<Expression>();
	// assignments of test data to locations + initialization of
	// object references
	ImmutableList<Statement> assignments = ImmutableSLList.<Statement> nil();
	for (int i = 0; i < nonPrim.length; i++) {
	    final EquivalenceClass nonPrimEqvClass = nonPrim[i];

	    final ImmutableSet<Term> locs = nonPrimEqvClass.getLocations();
	    final Iterator<Term> itt = locs.iterator();
	    if (!nonPrimEqvClass.isNull()) {
		final Term nonPrimLocTerm = itt.next();
		final Expression loc1 = translateTerm(nonPrimLocTerm, null,
		        null);
		final Expression constrCall = createConstructorCall(
		        nonPrimLocTerm.sort(), array2Cons, loc1,
		        nonPrimEqvClass.getKeYJavaType());

		if (locs.size() > 1) {
		    final ProgramVariable pv = new LocationVariable(
			    new ProgramElementName("_init" + i),
			    nonPrimEqvClass.getKeYJavaType());
		    final VariableSpecification varSpec = new VariableSpecification(
			    pv, constrCall, nonPrimEqvClass.getKeYJavaType());
		    assignments = assignments.append(new LocalVariableDeclaration(new TypeRef(
			            nonPrimEqvClass.getKeYJavaType()), varSpec));
		    loc2constrCall.put(loc1, pv);
		    while (itt.hasNext()) {
			final Expression loc2 = translateTerm(itt.next(), null,
			        null);
			addOrdered(loc2, locationsOrdered);
			loc2constrCall.put(loc2, pv);
		    }
		} else {
		    loc2constrCall.put(loc1, constrCall);
		}
		addOrdered(loc1, locationsOrdered);
	    } else { // nonPrimEqvClass.isNull
		while (itt.hasNext()) {
		    final Term locTerm = itt.next();
		    if (locTerm.op() != Op.NULL) {
			final Expression loc2 = translateTerm(locTerm, null,
			        null);
			addOrdered(loc2, locationsOrdered);
			loc2constrCall.put(loc2, NullLiteral.NULL);
		    }
		}
	    }
	}
	for (final Expression aLocationsOrdered : locationsOrdered) {
	    final Expression loc = aLocationsOrdered;
	    final Expression constrCall = loc2constrCall.get(loc);
	    final IndexReplaceVisitor irv = new IndexReplaceVisitor(loc,
		    testLocation, singleTuple, partCounter, testArray, serv);
	    irv.start();
	    irv.result();
	    assignments = assignments.append(ag.assignmentOrSet(
		    (Expression) irv.result(), constrCall, serv));
	}
	assignments = assignments.append(testDataAssignments);
	final Statement[] ib = new Statement[6 + code.length];
	// assignments = removeOutOfBounds(assignments);
	ib[0] = new StatementBlock(assignments
	        .toArray(new Statement[assignments.size()]));
	System.arraycopy(code, 0, ib, 1, code.length);
	final SyntacticalTypeRef stringBufferType = new SyntacticalTypeRef(
	        new ClassDeclaration(new ProgramElementName("StringBuffer"),
	                new ProgramElementName("java.lang.StringBuffer")));
	final New cons = new New(new Expression[0], stringBufferType, null);
	final SyntacticalProgramVariable buffer = new SyntacticalProgramVariable(
	        new ProgramElementName("buffer"), stringBufferType.type);
	ib[code.length + 1] = new LocalVariableDeclaration(stringBufferType,
	        new VariableSpecification(buffer, buffer.type));
	ib[code.length + 2] = new CopyAssignment(buffer, cons);

	final ProgramVariable result = new LocationVariable(
	        new ProgramElementName(RESULT_NAME), booleanType);
	ib[code.length + 3] = new LocalVariableDeclaration(new TypeRef(
	        booleanType), new VariableSpecification(result));
	final MethodReference oracle = getOracle(post, buffer, children);
	ib[code.length + 4] = new CopyAssignment(result, oracle);

	// The "/" has caused a problem with GenUTest
	Expression failure = new StringLiteral("\\nPost evaluated to false.\\n"
	        + "Variable or Location Assignments:\\n");
	for (int i = 0; i < testLocation.length; i++) {
	    for (int j = 0; j < testLocation[i].length; j++) {
		final Expression assignment = new Plus(new StringLiteral("  "
		        + testLocation[i][j].toString() + " = "),
		        singleTuple ? testArray[i] : new ArrayReference(
		                testArray[i], new Expression[] { partCounter }));
		failure = new Plus(failure, assignment);
	    }
	}
	Expression str = new Plus(new StringLiteral(
	        "\\nEvaluation of subformulas so far: "), new MethodReference(
	        new ImmutableArray<Expression>(), new ProgramElementName(
	                "toString"), buffer));
	str = new Plus(failure, str);
	ib[code.length + 5] = new MethodReference(
	        new ImmutableArray<Expression>(new Expression[] { str, result }),
	        new ProgramElementName("assertTrue"), null);
	Statement body = new StatementBlock(ib);

	// nested loops for executing the tested code with every possible
	// combination of testdata in each partition
	if (!singleTuple) {

	    // loop over the number of partitions
	    final VariableSpecification counterSpec = new VariableSpecification(
		    partCounter, new IntLiteral(0), intType);
	    final LocalVariableDeclaration counterDecl = new LocalVariableDeclaration(
		    new TypeRef(intType), counterSpec);
	    final Expression guard = new LessThan(partCounter,
		    testData.length == 0 ? new IntLiteral(1)
		            : new FieldReference(new LocationVariable(
		                    new ProgramElementName("length"), intType),
		                    testArray[0]));
	    body = new For(new LoopInitializer[] { counterDecl }, guard,
		    new Expression[] { new PostIncrement(partCounter) }, body);
	}

	s = s.append(body);
	l.add(replace(new StatementBlock(s.toArray(new Statement[s.size()]))));
	l.add(new Comment("\n  Covered execution trace:\n"
	        + mg.getExecutionTrace()));
	final MethodDeclaration tm = new MethodDeclaration(l, false);

	if (VisualDebugger.isDebuggingMode()) {
	    VisualDebugger.getVisualDebugger().addTestCase(fileName, name,
		    mg.getOriginalNode());
	}

	return tm;
    }

    /**
     * @param array2Cons
     *            maps an array expression to a constructor call for the array
     *            with dimension initialized by test data
     */
    protected Expression createConstructorCall(final Sort sort,
	    final HashMap<String, NewArray> array2Cons, final Expression loc1,
	    final KeYJavaType locKJT) {
	if (sort instanceof ArraySort) {
	    final String arrayExpression = CompilableJavaCardPP.toString(loc1);
	    final Expression cons = array2Cons.get(arrayExpression);
	    if (cons == null) {
		System.err
		        .println("WARNING:Problem with generating an array constructor for "
		                + arrayExpression
		                + "  An array of size 20 will be created but this is an emergency solution.");
		return new NewArray(new Expression[] { new IntLiteral(20) },
		        new TypeRef(getBaseType(locKJT)), locKJT, null, 0);
	    } else {
		return cons;
	    }
	    /*
	     * KeYJavaType locKJT =loc1.getKeYJavaType(serv, null); ExtList
	     * aType = new ExtList(); aType.add(new TypeRef(locKJT)); cons = new
	     * NewArray(aType, locKJT, new ArrayInitializer(new ExtList()), 0);
	     */
	} else {
	    return new New(new Expression[0], new TypeRef(locKJT), null);
	}
    }

    /**
     * Writes declarations and initilisations for ProgramVariables that haven't
     * been declared
     * 
     * @param reducedPVSet
     *            All not declared ProgramVariables
     * @return ImmutableList<Statement> a list of statements
     */
    private ImmutableList<Statement> declareAndInitProgVars(
	    final ImmutableSet<ProgramVariable> reducedPVSet) {
	ImmutableList<Statement> s = ImmutableSLList.<Statement> nil();
	// declare and initialize program variables
	for (final ProgramVariable element : reducedPVSet) {
	    VariableSpecification varSpec = null;
	    if (element.getKeYJavaType().getSort().extendsTrans(
		    serv.getTypeConverter().getIntegerLDT().targetSort())) {
		varSpec = new VariableSpecification(element, new TypeCast(
		        new IntLiteral(0),
		        new TypeRef(element.getKeYJavaType())), element
		        .getKeYJavaType());
	    } else if (element.getKeYJavaType().getSort() == booleanType
		    .getSort()) {
		varSpec = new VariableSpecification(element,
		        BooleanLiteral.TRUE, element.getKeYJavaType());
	    } else {
		/*
	         * varSpec = new VariableSpecification( pvsNotDecl[i], new New(
	         * new Expression[0], new
	         * TypeRef(pvsNotDecl[i].getKeYJavaType()), null),
	         * pvsNotDecl[i].getKeYJavaType());
	         */
		varSpec = new VariableSpecification(element, NullLiteral.NULL,
		        element.getKeYJavaType());
	    }
	    final LocalVariableDeclaration lvd = new LocalVariableDeclaration(
		    new TypeRef(element.getKeYJavaType()), varSpec);
	    s = s.append(lvd);
	}
	return s;
    }

    /**
     * @param l
     * @param singleTuple
     * @param testLocEqvs
     * @return an Array of Programvariables
     */
    private ProgramVariable[] initTestDataArr(final int l,
	    final boolean singleTuple, final EquivalenceClass[] testLocEqvs) {
	final ProgramVariable[] testArray = new ProgramVariable[l];
	for (int i = 0; i < l; i++) {
	    final KeYJavaType kjt = testLocEqvs[i].getKeYJavaType();
	    if (singleTuple) {
		testArray[i] = new LocationVariable(new ProgramElementName(
		        "testData" + i), kjt);
	    } else {
		testArray[i] = new LocationVariable(new ProgramElementName(
		        "testData" + i), getArrayTypeAndEnsureExistence(kjt, 1));
	    }
	}
	return testArray;
    }

    /**
     * @param l
     * @param singleTuple
     * @param testLocEqvs
     * @param testArray
     * @param s
     * @param testData
     * @return statements cotaining test values
     */
    @SuppressWarnings( { "unchecked" })
    private ImmutableList<Statement> appendStatements(final int l,
	    final boolean singleTuple, final EquivalenceClass[] testLocEqvs,
	    final ProgramVariable[] testArray, ImmutableList<Statement> s,
	    final Expression[][] testData) {
	final Random rand = new Random();
	VariableSpecification vs;
	for (int i = 0; i < l; i++) {
	    final KeYJavaType kjt = testLocEqvs[i].getKeYJavaType();
	    if (singleTuple) {
		Expression testDatum;
		if (testData[i][0] != null) {
		    testDatum = new TypeCast(testData[i][0], new TypeRef(kjt));
		} else {
		    testDatum = new TypeCast(new IntLiteral(rand.nextInt()),
			    new TypeRef(kjt));
		}

		vs = new VariableSpecification(testArray[i], testDatum, kjt
		        .getJavaType());
		s = s.append(new LocalVariableDeclaration(new TypeRef(kjt),
		                vs));
	    } else {
		final KeYJavaType akjt = getArrayTypeAndEnsureExistence(kjt, 1);
		final ExtList ai = new ExtList();
		for (int j = 0; j < testData[i].length; j++) {
		    if (testData[i][j] != null) {
			ai.add(new TypeCast(testData[i][j], new TypeRef(kjt)));
		    } else {
			ai.add(new TypeCast(new IntLiteral(rand.nextInt()),
			        new TypeRef(kjt)));
		    }
		}

		final ExtList aType = new ExtList();
		aType.add(new TypeRef(kjt));
		final NewArray init = new NewArray(aType, kjt,
		        new ArrayInitializer(ai), 1);
		vs = new VariableSpecification(testArray[i], init, akjt
		        .getJavaType());
		s = s.append(new LocalVariableDeclaration(new TypeRef(akjt),
		                vs));
	    }
	}
	return s;
    }

    private void addOrdered(final Expression e, final LinkedList<Expression> l) {
	for (int i = 0; i < l.size(); i++) {
	    if (depth(l.get(i)) > depth(e)) {
		l.add(i, e);
		return;
	    }
	}
	l.add(e);
    }

    private boolean singleTuple(final Expression[][] e) {
	if (0 < e.length) {
	    return e[0].length == 1;
	}
	return true;
    }

    /**
     * Returns the depth, i.e. the length of the reference prefix of an
     * expression.
     */
    private int depth(final Expression e) {
	if ((e instanceof FieldReference)
	        && (((FieldReference) e).getReferencePrefix() instanceof Expression)) {
	    return 1 + depth((Expression) ((FieldReference) e)
		    .getReferencePrefix());
	} else if ((e instanceof ArrayReference)
	        && (((ArrayReference) e).getReferencePrefix() instanceof Expression)) {
	    return depth((Expression) ((ArrayReference) e).getReferencePrefix()) + 1;
	}
	return 0;
    }

    /**
     * In order to combine KeY with GenUTest the test suite must have a main
     * method that calls the testmethods. This method extends the ExtList l with
     * a declaration of the main() method.
     * 
     * @author Christoph Gladisch
     */
    @SuppressWarnings("unchecked")
    private ExtList createMain(final ExtList l,
	    final Vector<MethodDeclaration> testMethods) {
	final ExtList el = new ExtList();
	el.add(new ProgramElementName("main"));
	el.add(new Public());
	el.add(new Static());
	final LinkedList<ParameterDeclaration> params = new LinkedList<ParameterDeclaration>();
	final SyntacticalArrayType t = new SyntacticalArrayType("java.lang",
	        "String", 1);
	final SyntacticalProgramVariable syntArg = new SyntacticalProgramVariable(
	        new ProgramElementName("arg"), t);
	params.add(new ParameterDeclaration(new Modifier[0],
	        new SyntacticalTypeRef(t), new VariableSpecification(syntArg,
	                syntArg.type), false));
	el.addAll(params);

	final ProgramElementName className = new ProgramElementName(fileName);
	final SyntacticalTypeRef syntr2 = new SyntacticalTypeRef(
	        new SyntacticalArrayType(null, className, 0));

	final New cons = new New(new Expression[0], syntr2, null);
	final SyntacticalProgramVariable testSuiteObject = new SyntacticalProgramVariable(
	        new ProgramElementName("testSuiteObject"), syntr2.type);
	int statementCount = 0;
	final Statement[] ib = new Statement[testMethods.size() + 2];

	final VariableSpecification varSpec = new VariableSpecification(
	        testSuiteObject, testSuiteObject.type);
	ib[statementCount++] = new LocalVariableDeclaration(syntr2, varSpec);
	ib[statementCount++] = new CopyAssignment(testSuiteObject, cons);
	final ReferencePrefix pref = testSuiteObject;

	for (int i = 0; i < testMethods.size(); i++) {
	    ib[statementCount++] = new MethodReference(
		    new ImmutableArray<Expression>(new Expression[] {}),
		    new ProgramElementName(testMethods.elementAt(i).getName()),
		    pref);
	}
	final Statement body = new StatementBlock(ib);
	final StatementBlock mBody = new StatementBlock(body);
	el.add(mBody);
	final MethodDeclaration tm = new MethodDeclaration(el, false);
	l.add(tm);
	return l;
    }

    /**
     * Exports the code under test to files and adds get and set methods for
     * each field.
     */
    protected abstract void exportCodeUnderTest();

    private String clean(String s) {
	while (s.indexOf(";.") != -1) {
	    s = s.substring(0, s.indexOf(";."))
		    + s.substring(s.indexOf(";.") + 1);
	}
	while (s.indexOf(";;") != -1) {
	    s = s.substring(0, s.indexOf(";;"))
		    + s.substring(s.indexOf(";;") + 1);
	}
	while (s.indexOf(";[") != -1) {
	    s = s.substring(0, s.indexOf(";["))
		    + s.substring(s.indexOf(";[") + 1);
	}
	while (s.indexOf(";]") != -1) {
	    s = s.substring(0, s.indexOf(";]"))
		    + s.substring(s.indexOf(";]") + 1);
	}
	return s;
    }

    /**
     * Returns the header consisting of package and import statements occuring
     * in the file <code>fileName</code>.
     */
    protected abstract String getHeader(final String fName);

    private String addImports(final String classDec, final PackageReference pr) {
	String imports = "import junit.framework.*;";
	if (pr != null) {
	    imports += "\nimport " + pr + ".*;";
	}
	return imports + "\n\n" + classDec;
    }

    /**
     * Creates a testoracle from the term <code>post</code>.
     * 
     * @param post
     *            the term used for creating a testoracle.
     * @param buffer
     *            a program variable of type StringBuffer.
     * @param children
     *            the children of the enclosing class. The MethodDeclarations
     *            created by this method are added to <code>children</code>.
     */
    protected MethodReference getOracle(Term post,
	    final SyntacticalProgramVariable buffer, final ExtList children) {
	post = replaceConstants(post, serv, null);
	return (MethodReference) getMethodReferenceForFormula(post, buffer,
	        children);
    }

    /**
     * Returns the method reference the term post is translated to and creates
     * also the corresponding method declaration.
     */
    @SuppressWarnings("unchecked")
    protected Expression getMethodReferenceForFormula(final Term post,
	    final SyntacticalProgramVariable buffer, final ExtList children) {
	if (post.sort() != Sort.FORMULA) {
	    return translateTerm(post, buffer, children);
	}
	if (translatedFormulas.containsKey(post)) {
	    return translatedFormulas.get(post);
	}
	final ExtList args = getArguments(post);
	args.add(buffer);
	final LinkedList<ParameterDeclaration> params = getParameterDeclarations(args);
	final Statement[] mBody = buildMethodBodyFromFormula(post, buffer,
	        children);
	final MethodDeclaration md = buildMethodDeclaration(mBody, new TypeRef(
	        booleanType), "subformula", params);
	children.add(md);
	final MethodReference mr = new MethodReference(args,
	        new ProgramElementName(md.getName()), testTypeRef);
	translatedFormulas.put(post, mr);
	return mr;
    }

    /**
     * Creates the method body for the method the term post is translated to.
     */
    private Statement[] buildMethodBodyFromFormula(final Term post,
	    final SyntacticalProgramVariable buffer, final ExtList children) {
	final Statement[] s = new Statement[4];
	final ProgramVariable result = new LocationVariable(
	        new ProgramElementName(RESULT_NAME), booleanType);
	s[0] = new LocalVariableDeclaration(new TypeRef(booleanType),
	        new VariableSpecification(result));
	final Expression f = translateFormula(post, buffer, children);
	s[1] = new CopyAssignment(result, f);
	StringLiteral sl = null;
	try {
	    // The following can go wrong because it uses the ordinary
	    // PrettyPrinter instead of CompilableJavaPP
	    // The ordinary PrettyPrinter does not handle classes defined in the
	    // package ppAnJavaASTExtension
	    sl = new StringLiteral("\\neval("
		    + ProofSaver.escapeCharacters(ProofSaver.printTerm(post,
		            serv).toString()) + ") = ");
	} catch (final Exception ex) {
	    sl = new StringLiteral("\\neval(" + post + ") = ");
	}
	final Plus str = new Plus(sl, result);
	s[2] = new MethodReference(new ImmutableArray<Expression>(str),
	        new ProgramElementName("append"), buffer);
	s[3] = new Return(result);
	return s;
    }

    /**
     * Translates a term to a java expression.
     */
    @SuppressWarnings("unchecked")
    protected Expression translateTerm(final Term t,
	    final SyntacticalProgramVariable buffer, final ExtList children) {
	Expression result = null;
	final Operator op = t.op();
	if (op instanceof ProgramInLogic) {
	    final ExtList tchildren = new ExtList();
	    for (int i = 0; i < t.arity(); i++) {
		tchildren.add(translateTerm(t.sub(i), buffer, children));
	    }
	    return ((ProgramInLogic) op).convertToProgram(t, tchildren);
	} else if (op == Op.IF_THEN_ELSE) {
	    final ExtList l = new ExtList();
	    l.add(getMethodReferenceForFormula(t.sub(0), buffer, children));
	    l.add(translateTerm(t.sub(1), buffer, children));
	    l.add(translateTerm(t.sub(2), buffer, children));
	    result = new Conditional(l);
	    result = new ParenthesizedExpression(result);
	} else if (op instanceof Function) {
	    final String name = op.name().toString().intern();
	    if (name.equals("add") || name.equals("jadd")
		    || name.equals("addJint")) {
		result = new Plus(translateTerm(t.sub(0), buffer, children),
		        translateTerm(t.sub(1), buffer, children));
	    } else if (name.equals("sub") || name.equals("jsub")
		    || name.equals("subJint")) {
		result = new Minus(translateTerm(t.sub(0), buffer, children),
		        translateTerm(t.sub(1), buffer, children));
	    } else if (name.equals("neg") || name.equals("jneg")
		    || name.equals("negJint") || name.equals("neglit")) {
		result = new Negative(translateTerm(t.sub(0), buffer, children));
	    } else if (name.equals("mul") || name.equals("jmul")
		    || name.equals("mulJint")) {
		result = new Times(translateTerm(t.sub(0), buffer, children),
		        translateTerm(t.sub(1), buffer, children));
	    } else if (name.equals("div") || name.equals("jdiv")
		    || name.equals("divJint")) {
		result = new Divide(translateTerm(t.sub(0), buffer, children),
		        translateTerm(t.sub(1), buffer, children));
	    } else if (name.equals("mod") || name.equals("jmod")
		    || name.equals("modJint")) {
		result = new Modulo(translateTerm(t.sub(0), buffer, children),
		        translateTerm(t.sub(1), buffer, children));
	    } else if (name.equals("Z")) {
		result = translateTerm(t.sub(0), buffer, children);
	    } else if (op instanceof CastFunctionSymbol) {
		final CastFunctionSymbol cast = (CastFunctionSymbol) op;
		Type type = null;
		try {
		    type = serv.getTypeConverter().getModelFor(
			    cast.getSortDependingOn()).javaType();
		} catch (final NullPointerException e) {
		    type = serv.getJavaInfo().getKeYJavaType(
			    cast.getSortDependingOn());
		}
		result = translateTerm(t.sub(0), buffer, children);
		// chrisg 12.5.2009: A cast expression must be created
		result = new TypeCast(result, new SyntacticalTypeRef(type));
	    }
	    if (result != null && !(result instanceof ParenthesizedExpression)) {
		result = new ParenthesizedExpression(result);
	    }
	}
	if (result == null) {
	    try {
		result = convertToProgramElement(t);
	    } catch (final Exception e) {
		throw new RuntimeException(
		        "The exception \n"
		                + e.getMessage()
		                + "\nwas thrown. It is possible, that this is caused by the wrong default behavior in translateTerm !");
	    }

	}
	return result;
    }

    /**
     * Translates a formula to a java expression, i.e. an oracle for the is
     * created
     * 
     * @param children
     *            the children of the enclosing class. The method declarations
     *            created by this method are added to <code>
 *         children</code> .
     */
    @SuppressWarnings("unchecked")
    private Expression translateFormula(final Term post,
	    final SyntacticalProgramVariable buffer, final ExtList children) {
	// final int tmp = post.toString().indexOf("banking.Account::cast");
	final ExtList l = new ExtList();
	if (post.sort() != Sort.FORMULA) {
	    return translateTerm(post, buffer, children);
	} else if (post.op() == Op.TRUE) {
	    return BooleanLiteral.TRUE;
	} else if (post.op() == Op.FALSE) {
	    return BooleanLiteral.FALSE;
	} else if (post.op() == Op.NOT) {
	    l.add(new ParenthesizedExpression(translateFormula(post.sub(0),
		    buffer, children)));
	    return new LogicalNot(l);
	} else if (post.op() == Op.AND) {
	    return new LogicalAnd(getMethodReferenceForFormula(post.sub(0),
		    buffer, children), getMethodReferenceForFormula(
		    post.sub(1), buffer, children));
	} else if (post.op() == Op.OR) {
	    return new LogicalOr(getMethodReferenceForFormula(post.sub(0),
		    buffer, children), getMethodReferenceForFormula(
		    post.sub(1), buffer, children));
	} else if (post.op() == Op.IMP) {
	    l.add(getMethodReferenceForFormula(post.sub(0), buffer, children));
	    return new LogicalOr(new LogicalNot(l),
		    getMethodReferenceForFormula(post.sub(1), buffer, children));
	} else if (post.op() instanceof Equality) {
	    l.add(getMethodReferenceForFormula(post.sub(0), buffer, children));
	    l.add(getMethodReferenceForFormula(post.sub(1), buffer, children));
	    final Equals eq = new Equals(l);
	    return eq;
	} else if (post.op() == Op.IF_THEN_ELSE) {
	    l.add(getMethodReferenceForFormula(post.sub(0), buffer, children));
	    l.add(getMethodReferenceForFormula(post.sub(1), buffer, children));
	    l.add(getMethodReferenceForFormula(post.sub(2), buffer, children));
	    return new Conditional(l);
	} else if (post.op() == Op.ALL) {
	    return translateQuantifiedTerm(true, post, buffer, children);
	} else if (post.op() == Op.EX) {
	    return translateQuantifiedTerm(false, post, buffer, children);
	} else if (post.op().name().toString().equals("lt")) {
	    return new LessThan(translateTerm(post.sub(0), buffer, children),
		    translateTerm(post.sub(1), buffer, children));
	} else if (post.op().name().toString().equals("gt")) {
	    l.add(translateTerm(post.sub(0), buffer, children));
	    l.add(translateTerm(post.sub(1), buffer, children));
	    return new GreaterThan(l);
	} else if (post.op().name().toString().equals("geq")) {
	    l.add(translateTerm(post.sub(0), buffer, children));
	    l.add(translateTerm(post.sub(1), buffer, children));
	    return new GreaterOrEquals(l);
	} else if (post.op().name().toString().equals("leq")) {
	    return new LessOrEquals(
		    translateTerm(post.sub(0), buffer, children),
		    translateTerm(post.sub(1), buffer, children));
	}
	throw new NotTranslatableException("Test oracle could not be generated");
    }

    /**
     * Builds a method declaration with the provided name and type. Field
     * references o.a occuring in the method body are replaced by methodcalls
     * o._a().
     */
    @SuppressWarnings("unchecked")
    private MethodDeclaration buildMethodDeclaration(final Statement[] body,
	    final TypeRef type, final String name,
	    final LinkedList<ParameterDeclaration> params) {
	final ExtList l = new ExtList();
	l.add(new ProgramElementName(name + (mcounter++)));
	l.add(new Private());
	l.add(new Static());
	l.addAll(params);
	l.add(type);
	l.add(replace(new StatementBlock(body)));
	final MethodDeclaration md = new MethodDeclaration(l, false);
	return md;
    }

    /**
     * Creates an oracle for a quantified formula, which is only possible for
     * some classes of quantified formulas. If <code>t</code> doesn't belong to
     * one of these classes a NotTranslatableException is thrown.
     */
    @SuppressWarnings("unchecked")
    private Expression translateQuantifiedTerm(final boolean all, final Term t,
	    final SyntacticalProgramVariable buffer, final ExtList children) {
	final LogicVariable lv = (LogicVariable) t.varsBoundHere(0).last();
	if (t.varsBoundHere(0).size() > 1
	        || !(lv.sort() == intType.getSort() || lv.sort().toString()
	                .equals("jint"))) {
	    throw new NotTranslatableException("quantified Term " + t);
	}
	final ProgramVariable pv = new LocationVariable(new ProgramElementName(
	        "_" + lv.name() + (TestGenFac.counter++)), intType);
	final Term matrix = replaceLogicVariable(t.sub(0), lv, pv);
	final ArrayList<Expression> lower = new ArrayList<Expression>();
	final ArrayList<Expression> upper = new ArrayList<Expression>();
	getRangeValues(matrix, buffer, children, pv, serv.getTypeConverter()
	        .getIntegerLDT(), all, false, lower, upper);
	if (lower.size() == 0 || upper.size() == 0) {
	    throw new NotTranslatableException("quantified Term with matrix"
		    + matrix + "\nseems to have no bounds");
	}
	// Type of int[]
	final Type intArrType = new SyntacticalArrayType("",
	        new ProgramElementName("int"), 1);

	final Statement[] body = new Statement[6];
	// Local variable storing the result
	// The name used to be "result" causing a clash with the program
	// variable representing JMLs "\result"
	final ProgramVariable result = new LocationVariable(
	        new ProgramElementName("subFormResult"), booleanType);
	body[0] = new LocalVariableDeclaration(new TypeRef(booleanType),
	        new VariableSpecification(result, (all ? BooleanLiteral.TRUE
	                : BooleanLiteral.FALSE), booleanType.getJavaType()));
	// Local variable storing all the lower bounds
	final SyntacticalProgramVariable lowVar = new SyntacticalProgramVariable(
	        new ProgramElementName("lows"), intArrType);
	body[1] = new LocalVariableDeclaration(new SyntacticalTypeRef(intArrType),
	        new VariableSpecification(lowVar, new ArrayInitializer(lower
	                .toArray(new Expression[lower.size()])), intArrType));
	// Local variable storing all the upper bounds
	final SyntacticalProgramVariable upVar = new SyntacticalProgramVariable(
	        new ProgramElementName("ups"), intArrType);
	body[2] = new LocalVariableDeclaration(new SyntacticalTypeRef(intArrType),
	        new VariableSpecification(upVar, new ArrayInitializer(upper
	                .toArray(new Expression[upper.size()])), intArrType));
	;
	// Creating the loop
	body[3] = createEvalLoop(matrix, all, pv, lowVar, upVar, result, buffer,
	        children);
	// Creating the description string
	body[4] = createResString(result, buffer, t);
	// The return statement
	body[5] = new Return(result);

	final ExtList args = getArguments(t);
	args.add(buffer);
	final LinkedList<ParameterDeclaration> params = getParameterDeclarations(args);

	final MethodDeclaration md = buildMethodDeclaration(body, new TypeRef(
	        booleanType), "quantifierTerm", params);
	children.add(md);
	return new MethodReference(args, new ProgramElementName(md.getName()),
	        testTypeRef);
    }

    /**
     * Iterates through a formula and looks for a relation, that contains the
     * quantified variabel
     * 
     * @param t
     *            the insepcted term
     * @param buffer
     * @param children
     * @param qv
     *            the quantified variable
     * @param iLDT
     *            IntegerLDT
     * @param all
     *            a flag that distiguishes between forall and exists
     * @param neg
     *            a flag showing wether this formula is negated
     * @param lower
     *            the list of upper bounds
     * @param upper
     *            the list of lower bounds
     */
    private void getRangeValues(final Term t,
	    final SyntacticalProgramVariable buffer, final ExtList children,
	    final ProgramVariable qv, final IntegerLDT iLDT, final boolean all,
	    final boolean neg, final ArrayList<Expression> lower,
	    final ArrayList<Expression> upper) {
	// Already traversed to deep
	if (t.sort() != Sort.FORMULA) {
	    return;
	}
	final Operator op = t.op();
	// Quantifier are not wanted
	if (op == Op.ALL || op == Op.EX) {
	    return;
	}
	if (op instanceof Function) {
	    // Tries to get the bounds
	    getRelation(t, op, buffer, children, qv, iLDT, all, neg, lower,
		    upper);
	} else if (op instanceof Junctor) {
	    // Avoid TRUE and FALSE
	    if (op.arity() == 0) {
		return;
	    }
	    if (op == Op.NOT) {
		getRangeValues(t.sub(0), buffer, children, qv, iLDT, all, !neg,
		        lower, upper);
	    } else if (op == Op.AND && !neg || (op == Op.OR && neg)) {
		if (!all) {
		    getRangeValues(t.sub(0), buffer, children, qv, iLDT, all,
			    neg, lower, upper);
		    getRangeValues(t.sub(1), buffer, children, qv, iLDT, all,
			    neg, lower, upper);
		}
	    } else if (op == Op.OR && !neg || (op == Op.AND && neg)) {
		if (all) {
		    getRangeValues(t.sub(0), buffer, children, qv, iLDT, all,
			    neg, lower, upper);
		    getRangeValues(t.sub(1), buffer, children, qv, iLDT, all,
			    neg, lower, upper);
		}
	    } else if (op == Op.IMP) {
		if (neg != all) {
		    getRangeValues(t.sub(0), buffer, children, qv, iLDT, all,
			    !neg, lower, upper);
		    getRangeValues(t.sub(1), buffer, children, qv, iLDT, all,
			    neg, lower, upper);
		}
	    }
	}
    }

    /**
     * If the current term is a relation and one of its subterms is the
     * quantified variable this method add the other term to the list of upper-
     * respectivly lower-bounds
     * 
     * @param t
     *            the term to inspect
     * @param op
     *            the terms operator
     * @param buffer
     * @param children
     * @param qv
     *            the quantified variable
     * @param iLDT
     *            the IntegerLDT
     * @param all
     *            flag to distinguish forall ad exist
     * @param neg
     *            flag to show if this term is negated
     * @param lower
     *            list containing the lower bounds
     * @param upper
     *            list containing the upper bounds
     */
    private void getRelation(final Term t, final Operator op,
	    final SyntacticalProgramVariable buffer, final ExtList children,
	    final ProgramVariable qv, final IntegerLDT iLDT, final boolean all,
	    final boolean neg, final ArrayList<Expression> lower,
	    final ArrayList<Expression> upper) {
	// At which position is the bound
	final int bPos = (t.sub(0).op() == qv ? 1 : (t.sub(1).op() == qv ? 0
	        : -1));
	// If there isn't the qVar we don't continue
	if (bPos < 0) {
	    return;
	}
	// Is the qVar the first subterm (left)
	final boolean isQvarLeft = bPos == 1;

	// calculate the right situation
	final RelOp opi;
	if (op == iLDT.getLessThan()) {
	    opi = new RelOp(true, false, isQvarLeft, (all != neg));
	} else if (op == iLDT.getLessOrEquals()) {
	    opi = new RelOp(true, true, isQvarLeft, (all != neg));
	} else if (op == iLDT.getGreaterOrEquals()) {
	    opi = new RelOp(false, true, isQvarLeft, (all != neg));
	} else if (op == iLDT.getGreaterThan()) {
	    opi = new RelOp(false, false, isQvarLeft, (all != neg));
	} else {
	    return;
	}

	// Add the bound to the appropriate List
	if (opi.isLess()) {
	    if (opi.isEquals()) {
		upper.add(translateTerm(t.sub(bPos), buffer, children));
	    } else {
		upper.add(new Minus(
		        translateTerm(t.sub(bPos), buffer, children),
		        new IntLiteral(1)));
	    }
	} else {
	    if (opi.isEquals()) {
		lower.add(translateTerm(t.sub(bPos), buffer, children));
	    } else {
		lower.add(new Plus(
		        translateTerm(t.sub(bPos), buffer, children),
		        new IntLiteral(1)));
	    }
	}
    }

    
    /**
     * Create a Java method to calculate the min-/max-value of an array of values
     * @param min falg to decide if min or max is wanted
     * @return a Java method calculating the min-/max-element of an array
     */
    private MethodDeclaration createMinMaxMethod(final boolean min) {
	// the int[] type
	final Type intArrType = new SyntacticalArrayType("",
	        new ProgramElementName("int"), 1);
	// the parameter variable
	final SyntacticalProgramVariable parVar = new SyntacticalProgramVariable(
	        new ProgramElementName("elems"), intArrType);
	// Declaring the methods parameter
	final ParameterDeclaration param = new ParameterDeclaration(
	        new Modifier[0], new SyntacticalTypeRef(intArrType),
	        new VariableSpecification(parVar, intArrType), false);
	// Creating and returning the method
	return new MethodDeclaration(new Modifier[] { new Public(),
	        new Static() }, new SyntacticalTypeRef(intType), new ProgramElementName("get"
		        + (min ? "Min" : "Max") + "Element"),
	        new ImmutableArray<ParameterDeclaration>(param), null,
	        createBody(min, parVar), false);
    }

    private StatementBlock createBody(final boolean min,
	    final SyntacticalProgramVariable elems) {
	final Statement[] s = new Statement[4];
	final SyntacticalProgramVariable resVar = new SyntacticalProgramVariable(
	        new ProgramElementName("res"), intType);
	final VariableSpecification resSpec = new VariableSpecification(resVar,
	        intType);
	final TypeReference intTypeRef = new SyntacticalTypeRef(intType);
	s[0] = new LocalVariableDeclaration(intTypeRef, resSpec);
	s[1] = new CopyAssignment(resVar, new ArrayReference(elems,
	        new Expression[] { new IntLiteral(0) }));
	s[2] = createLoop(min, resVar, elems);
	s[3] = new Return(resVar);
	return new StatementBlock(s);
    }

    /**
     * Creates thecode for a loop to iterate through an array and return the
     * min- or max-value
     * 
     * @param min
     *            flag to decide if the minimum or maximum is wanted
     * @param resVar
     *            the Variable that is the min-/max-value
     * @param elems
     *            the array containing the values to iterate
     * @return a Java-for-loop statement
     */
    private Statement createLoop(final boolean min,
	    final SyntacticalProgramVariable resVar,
	    final SyntacticalProgramVariable elems) {
	// The loop variable
	final SyntacticalProgramVariable iVar = new SyntacticalProgramVariable(
	        new ProgramElementName("i"), intType);
	// Initialise the loop variable
	final LoopInitializer[] loopInit = { new LocalVariableDeclaration(
	        new SyntacticalTypeRef(intType), new VariableSpecification(
	                iVar, new IntLiteral(1), intType)) };
	// The current element in the iteration
	final Expression curElem = new ArrayReference(elems,
	        new Expression[] { iVar });
	// The condition that decides if the curElem is assigned as result
	final Expression cond;
	if (min) {
	    cond = new LessThan(curElem, resVar);
	} else {
	    cond = new GreaterThan(curElem, resVar);
	}
	// Creates and returns the loop
	return new For(loopInit, new LessThan(iVar,
	        new FieldReference(new LocationVariable(new ProgramElementName(
	                "length"), intType), elems)),
	        new Expression[] { new PostIncrement(iVar) }, new If(cond,
	                new Then(new CopyAssignment(resVar, curElem))));
    }

    /**
     * @param min
     *            a falg to decide if the getMax oder getMin method is wanted
     * @param ranges
     *            the set of lower/upper bounds
     * @return the methodreference to the getMinElement-/GetMaxElement-method
     *         with the appropriate parameter
     */
    private Expression callMinMax(final boolean min,
	    final SyntacticalProgramVariable ranges) {
	final ImmutableArray<Expression> params = new ImmutableArray<Expression>(
	        ranges);
	final ProgramElementName methName = new ProgramElementName("get"
	        + (min ? "Min" : "Max") + "Element");
	return new MethodReference(params, methName, testTypeRef);
    }

    /**
     * Creates a for loop to simulate the behaviour of an quantified formula
     * @param matrix the matrix of the quantifier
     * @param all flag to distinguish forall end exist
     * @param pv the loop variable
     * @param lowVar an variable denoting an array which contains all lower bounds 
     * @param upVar an variable denoting an array which contains all upper bounds
     * @param result a variable denoting a variable that holds the result
     * @param buffer
     * @param children
     * @return a Java-for-loop that evaluates a quantified formula
     */
    private Statement createEvalLoop(final Term matrix, final boolean all,
	    final ProgramVariable pv, final SyntacticalProgramVariable lowVar,
	    final SyntacticalProgramVariable upVar,
	    final ProgramVariable result,
	    final SyntacticalProgramVariable buffer, final ExtList children) {
	// Initialise the loop variable
	final LocalVariableDeclaration init = new LocalVariableDeclaration(
	        new TypeRef(intType), new VariableSpecification(pv, callMinMax(
	                false, lowVar), intType.getJavaType()));
	// Create the body being executed by the loop
	final Statement loopBody = new CopyAssignment(result,
	        all ? new LogicalAnd(result, getMethodReferenceForFormula(
	                matrix.sub(1), buffer, children)) : new LogicalOr(
	                result, getMethodReferenceForFormula(matrix.sub(1),
	                        buffer, children)));
	// Create and return the for-loop
	return new For(new LoopInitializer[] { init }, new LessOrEquals(pv,
	        callMinMax(true, upVar)), new Expression[] { new PostIncrement(
	        pv) }, new StatementBlock(loopBody));
    }

    /**
     * Creates the representation of the string that describes which code is
     * being tested
     * 
     * @param result
     *            the string
     * @param buffer
     * @param t
     * @return the append call to append a String
     */
    private Statement createResString(final ProgramVariable result,
	    final SyntacticalProgramVariable buffer, final Term t) {
	StringLiteral sl = null;
	try {
	    // The following can go wrong because it uses the ordinary
	    // PrettyPrinter instead of CompilableJavaPP
	    // The ordinary PrettyPrinter does not handle classes defined in the
	    // package ppAnJavaASTExtension
	    sl = new StringLiteral("\\neval("
		    + ProofSaver.escapeCharacters(ProofSaver.printTerm(t, serv)
		            .toString()) + ") = ");
	} catch (final Exception ex) {
	    sl = new StringLiteral("\\neval(" + t + ") = ");
	}
	final Plus str = new Plus(sl, result);
	return new MethodReference(new ImmutableArray<Expression>(str),
	        new ProgramElementName("append"), buffer);
    }

    /**
     * Returns the location variables occuring in t that are no attributes.
     */
    @SuppressWarnings("unchecked")
    private ExtList getArguments(final Term t) {
	ImmutableSet<ProgramVariable> programVars = DefaultImmutableSet
	        .<ProgramVariable> nil();
	final TermProgramVariableCollector pvColl = new TermProgramVariableCollector(
	        serv);
	t.execPreOrder(pvColl);
	for (final Location location : pvColl.result()) {
	    final ProgramVariable v = (ProgramVariable) location;
	    if (!v.isMember()) {
		programVars = programVars.add(v);
	    }
	}
	programVars = removeDublicates(programVars);
	final Iterator<ProgramVariable> it = programVars.iterator();
	final ExtList args = new ExtList();
	while (it.hasNext()) {
	    args.add(it.next());
	}
	return args;
    }

    private LinkedList<ParameterDeclaration> getParameterDeclarations(
	    final ExtList l) {
	final LinkedList<ParameterDeclaration> params = new LinkedList<ParameterDeclaration>();
	for (final Object aL : l) {
	    final IProgramVariable arg = (IProgramVariable) aL;
	    // Depending wether it's a ProgramVariable or
	    // SyntacticalProgramVariable
	    // the type has to be obtained in two different ways.
	    if (arg instanceof ProgramVariable) {// chris
		final KeYJavaType kjt = arg.getKeYJavaType();
		params
		        .add(new ParameterDeclaration(new Modifier[0],
		                new TypeRef(kjt),
		                new VariableSpecification(arg), false));
	    } else if (arg instanceof SyntacticalProgramVariable) {
		final SyntacticalProgramVariable syntArg = (SyntacticalProgramVariable) arg;
		params.add(new ParameterDeclaration(new Modifier[0],
		        new SyntacticalTypeRef(syntArg.type),
		        new VariableSpecification(arg, syntArg.type), false));
	    } else {
		throw new RuntimeException(
		        "Unexpected case: arg is instance of:" + arg);
	    }
	}
	return params;
    }

    /**
     * replaces all occurences of lv in t with pv.
     */
    @SuppressWarnings("unchecked")
    protected Term replaceLogicVariable(final Term t, final LogicVariable lv,
	    final ProgramVariable pv) {
	final TermFactory tf = TermFactory.DEFAULT;
	Term result = null;
	if (t.op() == lv) {
	    return tf.createVariableTerm(pv);
	} else {
	    final Term subTerms[] = new Term[t.arity()];
	    final ImmutableArray<QuantifiableVariable>[] quantVars = new ImmutableArray[t
		    .arity()];
	    for (int i = 0; i < t.arity(); i++) {
		quantVars[i] = t.varsBoundHere(i);
		subTerms[i] = replaceLogicVariable(t.sub(i), lv, pv);
	    }
	    final JavaBlock jb = t.javaBlock();
	    result = tf.createTerm(t.op(), subTerms, quantVars, jb);
	}
	return result;
    }

    /**
     * Converts <code>t</code> to a ProgramElement. If <code>t</code> is a
     * (skolem)constant, a new identically named ProgramVariable of the same
     * sort is returned.
     */
    private Expression convertToProgramElement(Term t) {
	t = replaceConstants(t, serv, null);
	return serv.getTypeConverter().convertToProgramElement(t);
    }

    public DataStorage getData() {
	return data;
    }

    public void setData(final DataStorage data) {
	this.data = data;
    }

    protected void printDeclaration(final CompilableJavaCardPP pp, final Type cl)
	    throws IOException {
	assert (cl instanceof ClassDeclaration || cl instanceof InterfaceDeclaration) : "Given parameter\n"
	        + cl
	        + "\nwas neither a ClassDeclaration nor an Interface Declaration";
	if (cl instanceof ClassDeclaration) {
	    pp.printClassDeclaration((ClassDeclaration) cl);
	} else {
	    pp.printInterfaceDeclaration((InterfaceDeclaration) cl);
	}
    }

    protected void writeToFile(final String dirN, final String fN,
	    final StringWriter sw) throws IOException {
	final File dir = new File(directory + dirN);
	if (!dir.exists()) {
	    dir.mkdirs();
	}
	// Flushing everything to the file
	final File pcFile = new File(dir, fN.substring(fN
	        .lastIndexOf(File.separator) + 1));
	final FileWriter fw = new FileWriter(pcFile);
	final BufferedWriter bw = new BufferedWriter(fw);
	bw.write(getHeader(dirN + fN));
	bw.write(clean(sw.toString()));
	bw.close();
    }

    /**
     * Replaces rigid constants by program variables.
     */
    @SuppressWarnings("unchecked")
    static Term replaceConstants(final Term t, final Services serv,
	    final Namespace newPVs) {
	final TermFactory tf = TermFactory.DEFAULT;
	Term result = null;
	if (t.op() instanceof RigidFunction && t.arity() == 0
	        && !"#".equals(t.op().name().toString())
	        && !"TRUE".equals(t.op().name().toString())
	        && !"FALSE".equals(t.op().name().toString())
	        && t.op() != Op.NULL) {
	    KeYJavaType kjt = serv.getJavaInfo().getKeYJavaType(
		    t.sort().toString());
	    if (t.sort().toString().startsWith("jint")) {
		kjt = serv.getJavaInfo().getKeYJavaType(
		        t.sort().toString().substring(1));
	    }
	    final ProgramVariable pv = new LocationVariable(
		    new ProgramElementName(t.op().name().toString()), kjt);
	    if (newPVs != null) {
		newPVs.add(pv);
	    }
	    return tf.createVariableTerm(pv);
	} else if (t.op() instanceof ProgramVariable) {
	    if (newPVs != null && !((ProgramVariable) t.op()).isStatic()) {
		newPVs.add(t.op());
	    }
	    return t;
	} else {
	    final Term subTerms[] = new Term[t.arity()];
	    final ImmutableArray<QuantifiableVariable>[] quantVars = new ImmutableArray[t
		    .arity()];
	    for (int i = 0; i < t.arity(); i++) {
		quantVars[i] = t.varsBoundHere(i);
		subTerms[i] = replaceConstants(t.sub(i), serv, newPVs);
	    }
	    final JavaBlock jb = t.javaBlock();
	    result = tf.createTerm(t.op(), subTerms, quantVars, jb);
	}
	return result;
    }

    public void clean() {
	if (modelGenThread != null) {
	    modelGenThread.stop();
	    System.out.println("Thread killed:" + modelGenThread.getName());
	    modelGenThread = null;
	}
    }

    private class ModelGeneratorRunnable implements Runnable {
	/**
	 * stores the result of the model generation. If the result is null then
	 * either the thread has not finished computation or an error occurred.
	 */
	public Model[] models = null;
	final ModelGenerator mg;
	protected boolean interrupted = false;

	ModelGeneratorRunnable(final ModelGenerator mg) {
	    this.mg = mg;
	    assert (mg != null);
	}

	public void run() {
	    models = mg.createModels();
	}

	protected boolean timeoutIsActive() {
	    return TestGenerator.modelCreationTimeout >= 0;
	}

	/**
	 * Uses ModelGenerato.modelCreationTimeout in order to terminate threads
	 * when time is exceeded
	 */
	public Model[] createModels() throws InterruptedException {
	    if (modelGenThread != null) {
		modelGenThread.stop();
	    }
	    modelGenThread = new Thread(this,
		    "Model generation thread for node " + mg.node.serialNr()
		            + " (leaf node was " + mg.originalNode.serialNr()
		            + ")");
	    modelGenThread.start();
	    boolean timeoutActive = timeoutIsActive();
	    if (timeoutActive) {
		modelGenThread
		        .join(((long) TestGenerator.modelCreationTimeout) * 1000l);
		// In the mean time, during the execution of modelGenThread, the
		// timeout
		// maybe set to infinity (i.e. -1) by e.g.
		// ModelGenerationGUIInterface
		// in order to give the user time to investigate model
		// generation.
		timeoutActive = TestGenerator.modelCreationTimeout >= 0;
		if (!timeoutIsActive()) {
		    modelGenThread.join();
		}
	    } else {
		modelGenThread.join();
	    }
	    // models = modelGeneration.models; //read the generated model
	    if (models == null && timeoutActive) {
		mg.terminateAsSoonAsPossible();
		modelGenThread.join(3000);// give the thread one more second
		// before it gets terminated
		// System.out.println("Contorlled termination");
		modelGenThread.stop();
		interrupted = true;
	    }
	    modelGenThread = null;

	    return models;
	}

	public boolean wasInterrupted() {
	    return interrupted;
	}
    }

    private class RelOp {

	private boolean less;

	private boolean equals;

	private RelOp(final boolean less, final boolean equals,
	        final boolean swapSign, final boolean negate) {
	    if (swapSign == negate) {
		this.less = !less;
	    } else {
		this.less = less;
	    }
	    if (negate) {
		this.equals = !equals;
	    } else {
		this.equals = equals;
	    }
	}

	private boolean isLess() {
	    return less;
	}

	private boolean isEquals() {
	    return equals;
	}
    }
}
