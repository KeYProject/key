/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen;

import java.io.IOException;
import java.nio.file.*;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;
import javax.lang.model.element.Modifier;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.model.Heap;
import de.uka.ilkd.key.smt.model.Model;
import de.uka.ilkd.key.smt.model.ObjectVal;
import de.uka.ilkd.key.testgen.oracle.OracleGenerator;
import de.uka.ilkd.key.testgen.oracle.OracleMethodCall;
import de.uka.ilkd.key.util.KeYConstants;

import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.java.StringUtil;

import com.squareup.javapoet.*;
import org.checkerframework.checker.nullness.qual.PolyNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static de.uka.ilkd.key.testgen.Constants.*;
import static de.uka.ilkd.key.testgen.TestgenUtils.*;

/**
 * @author gladisch
 * @author herda
 */
@NullMarked
public class TestCaseGenerator {
    /**
     * The Java source file extension with a leading dot.
     */
    public static final String JAVA_FILE_EXTENSION_WITH_DOT = ".java";

    private static final Logger LOGGER = LoggerFactory.getLogger(TestCaseGenerator.class);

    private static final AtomicInteger FILE_COUNTER = new AtomicInteger();

    /**
     * Classes of the Java environment needed by KeY can be placed in this subdirectory.
     */
    public static final String DONT_COPY = "aux";
    private static final ClassName JUNIT5_TEST_ANNOTATION =
        ClassName.get("org.junit.jupiter.api", "Test");


    private static final ClassName HASHSET_NAME = ClassName.get(HashSet.class);
    private static final ClassName SET_NAME = ClassName.get(Set.class);
    private static final ClassName MAP_NAME = ClassName.get(Map.class);

    private static final ParameterizedTypeName BOOL_SET =
        ParameterizedTypeName.get(SET_NAME, TypeName.BOOLEAN.box());
    private static final ParameterizedTypeName BOOL_HASHSET =
        ParameterizedTypeName.get(HASHSET_NAME, TypeName.BOOLEAN.box());

    private static final ParameterizedTypeName SET_INT =
        ParameterizedTypeName.get(SET_NAME, TypeName.INT.box());
    private static final ParameterizedTypeName HASHSET_INT =
        ParameterizedTypeName.get(HASHSET_NAME, TypeName.INT.box());

    private static final ParameterizedTypeName OBJECT_SET =
        ParameterizedTypeName.get(SET_NAME, TypeName.OBJECT);
    private static final ParameterizedTypeName OBJECT_HASHSET =
        ParameterizedTypeName.get(HASHSET_NAME, TypeName.OBJECT);

    private final Services services;
    private final boolean rflAsInternalClass;
    private final ReflectionClassCreator rflCreator;
    private final Path modDirName;
    private final OutputEnvironment outputFolder;
    private final Path outputModDir;
    private final Path outputDontCopy;
    private final TGReporter reporter;
    private final String fileName;
    private final String packageName;
    private final ProofInfo info;
    private final OracleGenerator oracleGenerator;
    private final List<MethodSpec> oracleMethods;
    private final OracleMethodCall oracleMethodCall;
    private final Set<Sort> sortDummyClass = new HashSet<>();
    private final List<JavaFile> dummyClasses = new ArrayList<>(8);

    private final TestGenerationSettings settings;

    public TestCaseGenerator(Proof proof, TestGenerationSettings settings, TGReporter log) {
        this.reporter = log;
        this.settings = settings;

        fileName = "TestGeneric" + TestCaseGenerator.FILE_COUNTER;
        this.rflAsInternalClass = settings.isRFLAsInternalClass();
        services = proof.getServices();

        modDirName = Objects.requireNonNull(services.getJavaModel().getModelDir(),
            "No Java Source given in the JavaModel");
        outputFolder = new OutputEnvironment(Paths.get(settings.getOutputFolderPath()),
            settings.isOnlyTestClasses());
        outputModDir = outputFolder.getSourceDir();
        outputDontCopy = outputModDir.resolve(TestCaseGenerator.DONT_COPY);

        info = new ProofInfo(proof);

        rflCreator = new ReflectionClassCreator();
        oracleGenerator = new OracleGenerator(services, rflCreator, settings.isUseRFL());
        oracleMethods = new LinkedList<>();
        oracleMethodCall = getOracleAssertion(oracleMethods);
        packageName = "";
    }

    public TypeName buildDummyClassForAbstractSort(Sort sort) {
        final JavaInfo jinfo = services.getJavaInfo();
        final KeYJavaType kjt = jinfo.getKeYJavaType(sort);
        final String className = getDummyClassNameFor(sort);
        if (!sortDummyClass.add(sort)) {
            return ClassName.get("", className);
        }

        var clazz = TypeSpec.classBuilder(className);
        // sb.append("import ").append(sort.declarationString()).append(";\n\n");
        clazz.addSuperinterface(ClassName.get("", sort.declarationString()));
        // TODO:extends or implements depending if it is a class or interface.

        for (IProgramMethod m : jinfo.getAllProgramMethods(kjt)) {
            if (m.getFullName().indexOf('<') > -1) {
                continue;
            }
            if (m.isPrivate() || m.isFinal() || !m.isAbstract()) {
                continue;
            }
            final MethodDeclaration md = m.getMethodDeclaration();
            var ms = MethodSpec.methodBuilder(m.getName());
            if (m.isProtected())
                ms.addModifiers(Modifier.PROTECTED);
            if (m.isPublic())
                ms.addModifiers(Modifier.PUBLIC);
            if (m.isFinal())
                ms.addModifiers(Modifier.FINAL);
            if (m.isStatic())
                ms.addModifiers(Modifier.STATIC);
            if (m.isSynchronized())
                ms.addModifiers(Modifier.SYNCHRONIZED);

            if (md.getTypeReference() != null) {
                ms.returns(getTypeName(md.getTypeReference()));
            }

            var pdIter = md.getParameters();
            int varcount = 0;
            for (ParameterDeclaration pd : pdIter) {
                var type = pd.getTypeReference() == null ? TypeName.VOID
                        : getTypeName(pd.getTypeReference());

                var name = pd.getVariables().isEmpty()
                        ? "var" + varcount
                        : pd.getVariables().iterator().next().getFullName();

                var ps = ParameterSpec.builder(type, name);
                if (pd.isFinal())
                    ps.addModifiers(Modifier.FINAL);
                ms.addParameter(ps.build());
                varcount++;
            }

            if (md.getThrown() != null) {
                ms.addException(getTypeName(md.getThrown().getTypeReferenceAt(0)));
            }
            if (md.getTypeReference() == null) {
                ms.addStatement(CodeBlock.builder().build());
            } else {
                final String type = md.getTypeReference().toString();
                if (isNumericType(type)) {
                    ms.addStatement("return 0");
                } else if (type.equals("boolean")) {
                    ms.addStatement("return true");
                } else if (type.equals("char")) {
                    ms.addStatement("return 'a'");
                } else {
                    boolean returnNull = true;
                    final String retType =
                        md.getTypeReference().getKeYJavaType().getSort().name().toString();
                    if (retType.equals("java.lang.String")) {
                        ms.addStatement("{ return $S;", className);
                        returnNull = false;
                    }
                    if (returnNull) {
                        ms.addStatement("return null;");
                    }
                }
            }
        }

        var jfile = JavaFile.builder("", clazz.build());
        dummyClasses.add(jfile.build());
        return ClassName.get("", className);
    }

    private void copyFiles(Path srcFolder, Path target) throws IOException {
        // We don't want to copy the Folder with API Reference
        if (srcFolder.equals(target))
            return;
        Files.walkFileTree(srcFolder, new SimpleFileVisitor<>() {
            @Override
            public FileVisitResult visitFile(Path file, BasicFileAttributes attrs)
                    throws IOException {
                var relFile = srcFolder.relativize(file);
                var tarFile = target.resolve(relFile);
                Files.copy(file, tarFile, StandardCopyOption.REPLACE_EXISTING);
                return FileVisitResult.CONTINUE;
            }

            @Override
            public FileVisitResult postVisitDirectory(Path dir, IOException exc) {
                if (dir.equals(outputDontCopy))
                    return FileVisitResult.SKIP_SUBTREE;
                return FileVisitResult.CONTINUE;
            }
        });
    }

    public void createDummyClasses() throws IOException {
        for (final var s : dummyClasses)
            s.writeTo(outputFolder.getTestSourceDir());
    }

    /**
     * Creates the RFL.java file, that provides setter and getter methods using the reflection API
     * as well as object creation functions based on the objenesis library.
     */
    public void writeRFLFile() throws IOException {
        var content = createRFLFileContent();
        var jfile = JavaFile.builder("", content).build();
        jfile.writeTo(outputFolder.getTestSourceDir());
    }

    /**
     * Used by the Eclipse integration to creat the content of the RFL file.
     *
     * @return The content of the RFL file.
     */
    public TypeSpec createRFLFileContent() {
        return rflCreator.createClass(rflAsInternalClass);
    }


    /**
     * Copy the involved classes without modification
     */
    public void exportCodeUnderTest() throws IOException {
        copyFiles(modDirName, outputModDir);
    }

    public OracleMethodCall getOracleAssertion(List<MethodSpec> oracleMethods) {
        JTerm postcondition = getPostCondition();

        var oracle = oracleGenerator.generateOracleMethod(postcondition);
        OracleMethodCall oracleCall = new OracleMethodCall(oracle, oracle.getArgs());
        oracleMethods.add(oracle.build());
        oracleGenerator.getOracleMethods().forEach(it -> oracleMethods.add(it.build()));

        LOGGER.debug("Modifier Set: {}",
            oracleGenerator.getOracleLocationSet(info.getModifiable()));

        return oracleCall;
    }

    private JTerm getPostCondition() {
        return info.getPostCondition();
    }

    /**
     * Entry function to the world of test case generation.
     *
     * @param problemSolvers
     * @return
     * @throws IOException
     */
    public String generateJUnitTestSuite(Collection<SMTSolver> problemSolvers) throws IOException {
        outputFolder.init();

        var testSuite = createTestCaseContent(problemSolvers);
        testSuite.writeTo(outputFolder.getTestSourceDir());
        reporter.writeln("Writing test file");

        exportCodeUnderTest();
        createDummyClasses();

        try {
            if (settings.isUseRFL()) {
                writeRFLFile();
            }
        } catch (Exception ex) {
            reporter.writeln("Error: The file RFL" + JAVA_FILE_EXTENSION_WITH_DOT
                + " is either not generated or it has an error.");
            LOGGER.error("Error: The file RFL {} is either not generated or it has an error.",
                JAVA_FILE_EXTENSION_WITH_DOT);
        }
        TestCaseGenerator.FILE_COUNTER.incrementAndGet();
        return testSuite.toString();
    }

    public JavaFile createTestCaseContent(Collection<SMTSolver> problemSolvers) {
        // TODO: Include package definition (same as type containing the proof obligation)

        var clazz = TypeSpec.classBuilder(ClassName.get(packageName, fileName));

        int counter = 0;
        for (final SMTSolver solver : problemSolvers) {
            try {
                var goal = solver.getProblem().getGoal();
                var node = goal.node();
                final String originalNodeName = node.proof().name().toString();
                var ms = MethodSpec.methodBuilder("testcode_" + counter);

                boolean success = false;
                if (solver.getSocket().getQuery() != null) {
                    final Model m = solver.getSocket().getQuery().getModel();
                    if (modelIsOK(m)) {
                        reporter.writeln("Generate: " + originalNodeName);
                        Map<String, Sort> typeInfMap = generateTypeInferenceMap(goal.node());
                        ms.addComment(originalNodeName);
                        ms.addAnnotation(JUNIT5_TEST_ANNOTATION);
                        ms.addComment("Test preamble: creating objects and intializing test data");
                        generateTestCase(ms, m, typeInfMap);

                        Set<JTerm> vars = new HashSet<>();
                        info.getProgramVariables(info.getPO(), vars);
                        ms.addComment("Other variables");
                        getRemainingConstants(ms, m.getConstants().keySet(), vars);
                        ms.addComment("Calling the method under test   ")
                                .addStatement(
                                    info.getCode()
                                            // clean up KeY-special syntax of "obj.method()@CLAZZ;
                                            .replaceAll("@.*?;", ";"));

                        var junit5Assertions =
                            ClassName.get("org.junit.jupiter.api", "Assertions");

                        ms.addComment("Calling the test oracle")
                                .addStatement("$T.assertTrue($L)", junit5Assertions,
                                    oracleMethodCall);
                        counter++;
                        success = true;
                        clazz.addMethod(ms.build());
                    }
                }
                if (!success) {
                    reporter.writeln(
                        "A model (test data) was not generated for:" + originalNodeName);
                }
            } catch (final Exception ex) {
                reporter.reportException(ex);
                reporter.writeln(
                    "A test case was not generated due to an exception. Continuing test generation...");
            }
        }

        if (counter == 0) {
            reporter.writeln(
                "Warning: no test case was generated. Adjust the SMT solver settings (e.g. timeout) "
                    + "in Options->SMT Solvers.");
        } else if (counter < problemSolvers.size()) {
            reporter.writeln("Warning: SMT solver could not solve all test data constraints. "
                + "Adjust the SMT solver settings (e.g. timeout) in Options->SMT Solvers.");
        }

        clazz.addMethod(getMainMethod(fileName, counter));

        clazz.addMethods(oracleMethods);

        if (rflAsInternalClass) {
            clazz.addType(createRFLFileContent());
        }

        var jfile = JavaFile.builder(packageName, clazz.build());
        jfile.addFileComment(
            """
                    This is a test driver generated by KeY $S (www.key-project.org).
                    $S
                    @author Christoph Gladisch
                    @author Mihai Herda
                    """,
            KeYConstants.VERSION, fileName + JAVA_FILE_EXTENSION_WITH_DOT);
        return jfile.build();
    }

    public TypeName inferSort(Map<String, Sort> typeInfMap, String progVar) {
        if (typeInfMap.containsKey(progVar)) {
            var sort = typeInfMap.get(progVar);
            return getSafeType(sort);
        }
        LOGGER.warn("Warning: inferSort did not find:  {}", progVar);
        return ClassName.get("", "NOTYPE");
    }

    public Map<String, Sort> generateTypeInferenceMap(Node n) {
        HashMap<String, Sort> typeInfMap = new HashMap<>();
        for (final SequentFormula sf : n.sequent()) {
            generateTypeInferenceMapHelper(sf.formula(), typeInfMap);
        }
        return typeInfMap;
    }

    private void generateTypeInferenceMapHelper(Term t,
            Map<String, Sort> map) {
        final var op = t.op();
        if (op instanceof ProgramVariable) {
            ProgramVariable pv = (ProgramVariable) t.op();
            final String name = pv.name().toString();
            if (map.containsKey(name)) {
                if (map.get(name) != pv.sort()) {
                    LOGGER.warn("Warning: ProgramVariable {} is ambiguous.", name);
                }
            } else {
                LOGGER.debug("PV {} Sort: {} KeYJavaType: {}", name, pv.sort(),
                    pv.getKeYJavaType());
                map.put(name, pv.sort());
            }
        } else if (op instanceof Function && !(op instanceof ObserverFunction)) {
            // This case collects fields of classes. The function itself has
            // sort "Field" because it is just the name of the field. To get
            // the actual class of the field
            Function func = (Function) t.op();
            String name = func.name().toString();
            Sort sort = func.sort();
            HeapLDT hLDT = services.getTypeConverter().getHeapLDT();
            if (sort == hLDT.getFieldSort()) {
                var pv = getProgramVariable(t);
                if (pv == null)
                    return;

                name = name.replace("::$", "::");

                if (map.containsKey(name)) {
                    if (map.get(name) != pv.sort()) {
                        LOGGER.warn("Function {} is ambiguous.", name);
                    }
                } else {
                    map.put(name, pv.sort());
                }
            }
        }

        for (int i = 0; i < t.arity(); i++) {
            generateTypeInferenceMapHelper(t.sub(i), map);
        }
    }

    @Nullable
    private ProgramVariable getProgramVariable(Term locationTerm) {
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        ProgramVariable result = null;
        // Make sure that the function is not an array
        if (locationTerm.op() instanceof JFunction function && heapLDT.getArr() != function) {
            String typeName = HeapLDT.getClassName(function);
            KeYJavaType type = services.getJavaInfo().getKeYJavaType(typeName);
            if (type != null) {
                String fieldName = HeapLDT.getPrettyFieldName(function);
                result = services.getJavaInfo().getAttribute(fieldName, type);
            }
        }
        return result;
    }

    private void getRemainingConstants(MethodSpec.Builder ms,
            Collection<String> existingConstants,
            Collection<JTerm> newConstants) {
        for (JTerm c : newConstants) {
            if (!existingConstants.contains(c.toString())) {
                String init = "null";
                if (c.sort().equals(services.getTypeConverter().getIntegerLDT().targetSort())) {
                    init = "0";
                } else if (c.sort()
                        .equals(services.getTypeConverter().getBooleanLDT().targetSort())) {
                    init = "false";
                }

                ms.addComment("Generated in getRemainingConstants");
                ms.addStatement("$T $L = $L", getSafeType(c.sort()), c, init);
                ms.addStatement("$T $L = $L", getSafeType(c.sort()), getPreName(c.toString()),
                    init);
            }
        }
    }


    private boolean isInPrestate(Collection<? extends ObjectVal> prestate, ObjectVal o) {
        return true;
        // return prestate.contains(o) &&
        // services.getTypeConverter().isReferenceType(
        // services.getJavaInfo().getKeYJavaType(o.getSort()).getJavaType())
    }

    private boolean isInPrestate(Collection<? extends ObjectVal> prestate, String name) {
        return true;
        // // TODO return only needed objects
        // for(ObjectVal o : prestate){
        // if (services.getTypeConverter().isReferenceType(
        // services.getJavaInfo().getKeYJavaType(o.getSort()).getJavaType())) {
        // String oName = createObjectName(o);
        // if(oName.equals(name)){
        // return true;
        // }
        // }
        // }
        //
        // return false;
    }

    public String generateModifierSetAssertions(Model m) {
        return TAB + "//Modifier set assertions";
    }

    public void generateTestCase(MethodSpec.Builder mb, Model m, Map<String, Sort> typeInfMap) {
        m.removeUnnecessaryObjects();

        Set<String> objects = new HashSet<>();

        Heap heap = null;
        for (final Heap h : m.getHeaps()) {
            if (h.getName().equals(HeapLDT.BASE_HEAP_NAME.toString())) {
                heap = h;
                break;
            }
        }

        // Set<ObjectVal> prestate = getPrestateObjects(m);
        Set<ObjectVal> prestate = new HashSet<>();
        if (heap != null) {
            // create objects
            for (final ObjectVal o : heap.getObjects()) {
                if (o.getName().equals("#o0")) {
                    continue;
                }
                final TypeName type = getSafeType(o.getSort());
                String right;
                if (type instanceof ArrayTypeName arrayTypeName) {
                    right = "new " + arrayTypeName.componentType + "[" + o.getLength() + "]";
                } else if (o.getSort() == null || o.getSort().toString().equals("Null")) {
                    right = "null";
                } else {
                    if (settings.isUseRFL()) {
                        right = "RFL.new" + ReflectionClassCreator.cleanTypeName(type) + "()";
                        rflCreator.addSort(type);
                        LOGGER.debug("Adding sort (create Object): {}", type);
                    } else {
                        right = "new " + type + "()";
                    }
                }

                String objName = createObjectName(o);
                objects.add(objName);
                mb.addStatement("$T $N = $L", type, objName, right)
                        .addStatement("$T $N = $L", type, getPreName(objName), right);

            }
        }


        // init constants
        for (final String c : m.getConstants().keySet()) {
            String val = m.getConstants().get(c);
            if (filterVal(val) && !c.equals("null")) {
                boolean isObject = false;
                boolean isLiteral = false;
                TypeName type = TypeName.INT;
                TypeName declType;
                if (val.equals("true") || val.equals("false")) {
                    type = TypeName.BOOLEAN;
                    isLiteral = true;
                } else if (StringUtil.isNumber(val)) {
                    isLiteral = true;
                } else if (val.startsWith("#o")) {
                    isObject = true;
                    type = this.inferSort(typeInfMap, c);
                }

                declType = type;
                val = translateValueExpression(val);
                mb.addComment("Generated in generateTestCases#600");
                mb.addStatement("$T $N = ($T) $L", declType, c, type, val);


                if ((isObject || Character.isJavaIdentifierStart(c.charAt(0)))
                        && isInPrestate(prestate, val)) {
                    mb.addComment("Generated in generateTestCases#606");
                    if (isLiteral) {
                        mb.addStatement("$T $N = ($T) $L", declType, getPreName(c), type, val);
                    } else {
                        mb.addStatement("$T $N = ($T) $L", declType, getPreName(c), type,
                            getPreName(val));
                    }
                }
            }
        }

        // init fields
        if (heap != null) {
            for (final ObjectVal o : heap.getObjects()) {
                if (o.getName().equals("#o0")
                        || o.getSort().name().toString().endsWith("Exception")) {
                    continue;
                }
                final String receiverObject = createObjectName(o);
                for (final String f : o.getFieldvalues().keySet()) {
                    if (f.contains("<") || f.contains(">")) {
                        continue;
                    }
                    String fieldName = f.substring(f.lastIndexOf(':') + 1);
                    fieldName = fieldName.replace("|", "");
                    String val = o.getFieldvalues().get(f);
                    String fieldName2 = f.replace("|", "");
                    final TypeName vType = inferSort(typeInfMap, fieldName2);
                    // possible bug if vType represents an abstract type or an interface. See:
                    // getSafeType.
                    rflCreator.addSort(vType);

                    LOGGER.debug("Added sort (init fields): {}", vType);
                    val = translateValueExpression(val);
                    final TypeName rcObjType = getSafeType(o.getSort());

                    if (rcObjType != null) { // add cast
                        mb.addStatement("(($T)%N).$N = ($T) %N",
                            rcObjType, receiverObject, fieldName, vType, val);
                    } else {
                        mb.addStatement("%N.$N = ($T) %N",
                            receiverObject, fieldName, vType, val);
                    }


                    if (isInPrestate(prestate, o)) {
                        // if value that is pointed to is object and in prestate then use prestate
                        // object
                        if (!vType.equals("int") && !vType.equals("boolean")
                                && isInPrestate(prestate, val) && !val.equals("null")) {
                            val = getPreName(val);
                        }

                        if (rcObjType != null) { // add cast
                            mb.addStatement("(($T)%N).$N = ($T) %N",
                                rcObjType, receiverObject, fieldName, vType, val);
                        } else {
                            mb.addStatement("%N.$N = ($T) %N",
                                receiverObject, fieldName, vType, val);
                        }
                    }

                }
                if (o.getSort() != null && o.getSort() instanceof ArraySort) {
                    var safeType = (ArrayTypeName) getSafeType(o.getSort());
                    var elementType = safeType.componentType;
                    rflCreator.addSort(safeType);
                    LOGGER.debug("Added sort (init array fields): {}", safeType);

                    for (int i = 0; i < o.getLength(); i++) {
                        String val = o.getArrayValue(i);
                        val = translateValueExpression(val);

                        mb.addStatement("$N[$L] = $L", receiverObject, i, val);

                        if (isInPrestate(prestate, o)) {
                            if (!isPrimitiveType(elementType) && isInPrestate(prestate, val)
                                    && !val.equals("null")) {
                                val = getPreName(val);
                            }
                            mb.addStatement("$N[$L] = $L", getPreName(receiverObject), i, val);
                        }
                    }
                }
            }
        }


        createOldMap(mb, objects);
        createBoolSet(mb);
        createIntSet(mb);
        createObjSet(mb, heap);
    }

    private static final ClassName NAME_HASH_MAP = ClassName.get(HashMap.class);

    private void createOldMap(MethodSpec.Builder mb, Set<String> objNames) {
        mb.addComment("Generated in createOldMap()");
        var map =
            ParameterizedTypeName.get(NAME_HASH_MAP, ClassName.OBJECT, ClassName.OBJECT);
        mb.addStatement("$T $N = new $T()", map, OLD_MAP, map);
        for (String o : objNames) {
            mb.addStatement("$N.put($N, $L)", OLD_MAP, getPreName(o), o);
        }
    }

    private String getPreName(String val) {
        return OracleGenerator.PRE_STRING + val;
    }

    private String createObjectName(final ObjectVal o) {
        return o.getName().replace("#", "_");
    }

    private String getDummyClassNameFor(Sort sort) {
        final JavaInfo jinfo = services.getJavaInfo();
        final KeYJavaType kjt = jinfo.getKeYJavaType(sort);
        return kjt.getName() + DUMMY_POSTFIX;
    }

    private MethodSpec getMainMethod(String className, int i) {
        var main = MethodSpec.methodBuilder("main")
                .addModifiers(Modifier.PUBLIC, Modifier.STATIC, Modifier.FINAL)
                .addParameter(String[].class, "args")
                .build();

        var clazz = TypeSpec.classBuilder(className);
        clazz.addMethod(main);
        return main;
    }


    private void createBoolSet(MethodSpec.Builder mb) {
        // bool
        mb.addStatement("$T $N = new $T()", BOOL_SET, ALL_BOOLS, BOOL_HASHSET);
        mb.addStatement("$N.add($L)", ALL_BOOLS, true);
        mb.addStatement("$N.add($L)", ALL_BOOLS, false);
    }

    private static void createIntSet(MethodSpec.Builder mb) {
        long size = ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings().getIntBound();
        long low = (long) -Math.pow(2, size - 1);
        long hi = (long) (Math.pow(2, size - 1) - 1);

        mb.addStatement("$T $N = new $T()", SET_INT, ALL_INTS, HASHSET_INT);
        for (long i = low; i <= hi; i++) {
            mb.addStatement("$N.add($L)", ALL_INTS, i);
        }
    }

    private void createObjSet(MethodSpec.Builder mb, Heap h) {
        mb.addStatement("$T $N = new $T()", OBJECT_SET, ALL_OBJECTS, OBJECT_HASHSET);

        for (ObjectVal o : h.getObjects()) {
            String name = o.getName();
            if (name.equals("#o0")) {
                continue;
            }
            name = name.replace("#", "_");
            mb.addStatement("$N.add($N)", ALL_OBJECTS, name);
        }
    }

    @PolyNull
    public @Nullable TypeName getSafeType(@Nullable Sort sort) {
        if (sort == null) {
            return null;
        }

        if (sort instanceof ArraySort as) {
            final TypeName safeType = getSafeType(as.elementSort());
            return ArrayTypeName.of(Objects.requireNonNull(safeType));
        }

        if (sort.isAbstract()) {
            return buildDummyClassForAbstractSort(sort);
        }
        return getTypeName(sort);
    }

    public static TypeName getTypeName(Sort sort) {
        if (sort instanceof ArraySort as) {
            final TypeName safeType = getTypeName(as.elementSort());
            return ArrayTypeName.of(Objects.requireNonNull(safeType));
        }

        String typename = sort.name().toString();

        return switch (typename) {
            case "Set<Boolean>" -> BOOL_SET;
            case "Map<Object,Object>" ->
                ParameterizedTypeName.get(MAP_NAME, TypeName.OBJECT, TypeName.OBJECT);
            case "Null" -> TypeName.OBJECT;
            case "int" -> TypeName.INT;
            case "double", "real" -> TypeName.DOUBLE;
            case "bool" -> TypeName.BOOLEAN;
            default -> ClassName.get("", typename);
        };
    }

    private static TypeName getTypeName(TypeReference tr) {
        return ClassName.get("", tr.getName());
    }
}
