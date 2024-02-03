/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen;

import com.squareup.javapoet.*;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.model.Heap;
import de.uka.ilkd.key.smt.model.Model;
import de.uka.ilkd.key.smt.model.ObjectVal;
import de.uka.ilkd.key.testgen.oracle.OracleGenerator;
import de.uka.ilkd.key.testgen.oracle.OracleMethodCall;
import de.uka.ilkd.key.testgen.settings.TestGenerationSettings;
import de.uka.ilkd.key.testgen.smt.testgen.MemoryTestGenerationLog;
import de.uka.ilkd.key.testgen.smt.testgen.TestGenerationLog;
import de.uka.ilkd.key.util.KeYConstants;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.key_project.util.java.StringUtil;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.lang.model.element.Modifier;
import java.io.IOException;
import java.nio.file.*;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;

import static de.uka.ilkd.key.testgen.Format.JUnit4;
import static de.uka.ilkd.key.testgen.TestgenUtils.*;
import static de.uka.ilkd.key.testgen.template.Constants.*;

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
    private static final ClassName JUNIT4_TEST_ANNOTATION = ClassName.get("org.junit", "Test");
    private static final ClassName JUNIT5_TEST_ANNOTATION =
            ClassName.get("org.junit.jupiter.api", "Test");
    private static final ClassName TESTNG_TEST_ANNOTATION = ClassName.get("org.junit", "Test");
    private final Services services;
    private final boolean rflAsInternalClass;
    private final AssignmentCreator assignmentCreator;
    private final ReflectionClassCreator rflCreator;
    private final String modDirName;
    private final OutputEnvironment outputFolder;
    private final Path outputModDir;
    private final Path outputDontCopy;

    private final TestGenerationLog logger;
    private final String fileName;
    private final String packageName;
    private final String mutName;
    private final ProofInfo info;
    private final OracleGenerator oracleGenerator;
    private List<MethodSpec> oracleMethods = new ArrayList<>(0);
    @Nullable
    private String oracleMethodCall;
    private final Set<Sort> sortDummyClass = new HashSet<>();
    private final List<JavaFile> dummyClasses = new ArrayList<>(8);

    private final TestGenerationSettings settings;

    public TestCaseGenerator(Proof proof, TestGenerationSettings settings, @Nullable TestGenerationLog log) {
        logger = Objects.requireNonNullElse(log, new MemoryTestGenerationLog());
        this.settings = settings;

        fileName = "TestGeneric" + TestCaseGenerator.FILE_COUNTER;
        this.rflAsInternalClass = settings.isRFLAsInternalClass();
        services = proof.getServices();
        assignmentCreator = settings.useRFL()
                ? TestgenUtils::createAssignmentWithRfl
                : TestgenUtils::createAssignmentWithoutRfl;


        modDirName = services.getJavaModel().getModelDir();
        outputFolder = new OutputEnvironment(Paths.get(settings.getOutputFolderPath()));
        outputModDir = outputFolder.getSourceDir();
        outputDontCopy = outputModDir.resolve(TestCaseGenerator.DONT_COPY);

        info = new ProofInfo(proof);
        String mutCall = Objects.requireNonNullElse(info.getMUTCall(),
                "<method under test> //Manually write a call to the method under test, "
                        + "because KeY could not determine it automatically.");

        mutName = Objects.requireNonNull(info.getMUT()).getFullName();
        rflCreator = new ReflectionClassCreator();
        oracleGenerator = new OracleGenerator(services, rflCreator, settings.useRFL());
        if (settings.useJunit() == JUnit4) {
            oracleMethods = new LinkedList<>();
            oracleMethodCall = getOracleAssertion(oracleMethods);
        }
        packageName = "";
    }

    public String buildDummyClassForAbstractSort(Sort sort) {
        final JavaInfo jinfo = services.getJavaInfo();
        final KeYJavaType kjt = jinfo.getKeYJavaType(sort);
        final String className = getDummyClassNameFor(sort);
        if (!sortDummyClass.add(sort)) {
            return className;
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
                    try {
                        final String retType =
                                md.getTypeReference().getKeYJavaType().getSort().name().toString();
                        if (retType.equals("java.lang.String")) {
                            ms.addStatement("{ return $S;", className);
                            returnNull = false;
                        }
                    } catch (final Exception ignored) {
                    }

                    if (returnNull) {
                        ms.addStatement("return null;");
                    }
                }
            }
        }

        var jfile = JavaFile.builder("", clazz.build());
        dummyClasses.add(jfile.build());
        return className;
    }

    private static TypeName getTypeName(TypeReference tr) {
        return ClassName.get("", tr.getName());
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
        copyFiles(Paths.get(modDirName), outputModDir);
    }

    public String getOracleAssertion(List<MethodSpec> oracleMethods) {
        Term postcondition = getPostCondition();

        var oracle = oracleGenerator.generateOracleMethod(postcondition);
        OracleMethodCall oracleCall = new OracleMethodCall(oracle, oracle.getArgs());
        oracleMethods.add(oracle.build());
        oracleGenerator.getOracleMethods().forEach(it -> oracleMethods.add(it.build()));

        LOGGER.debug("Modifier Set: {}",
                oracleGenerator.getOracleLocationSet(info.getAssignable()));

        return "assertTrue(" + oracleCall + ");";
    }

    private Term getPostCondition() {
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
        logger.writeln("Writing test file");

        exportCodeUnderTest();
        createDummyClasses();

        try {
            if (settings.useRFL()) {
                writeRFLFile();
            }
        } catch (Exception ex) {
            logger.writeln("Error: The file RFL" + JAVA_FILE_EXTENSION_WITH_DOT
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
                        logger.writeln("Generate: " + originalNodeName);
                        Map<String, Sort> typeInfMap = generateTypeInferenceMap(goal.node());
                        ms.addComment(originalNodeName);
                        switch (settings.useJunit()) {
                            case JUnit4 -> ms.addAnnotation(JUNIT4_TEST_ANNOTATION);
                            case JUnit5 -> ms.addAnnotation(JUNIT5_TEST_ANNOTATION);
                            case TestNG -> ms.addAnnotation(TESTNG_TEST_ANNOTATION);
                            case Plain -> {
                            }
                        }
                        ms.addComment("Test preamble: creating objects and intializing test data");
                        generateTestCase(ms, m, typeInfMap);

                        Set<Term> vars = new HashSet<>();
                        info.getProgramVariables(info.getPO(), vars);
                        ms.addComment("Other variables")
                                .addStatement(
                                        getRemainingConstants(m.getConstants().keySet(), vars))
                                .addComment("   //Calling the method under test   ")
                                .addStatement(info.getCode());

                        if (isJunit()) {
                            ms.addComment("calling the test oracle").addStatement(oracleMethodCall);
                        }
                        counter++;
                        success = true;
                        clazz.addMethod(ms.build());
                    }
                }
                if (!success) {
                    logger.writeln("A model (test data) was not generated for:" + originalNodeName);
                }
            } catch (final Exception ex) {
                logger.writeException(ex);
                logger.writeln("A test case was not generated due to an exception. Continuing test generation...");
            }
        }

        if (counter == 0) {
            logger.writeln(
                    "Warning: no test case was generated. Adjust the SMT solver settings (e.g. timeout) "
                            + "in Options->SMT Solvers.");
        } else if (counter < problemSolvers.size()) {
            logger.writeln("Warning: SMT solver could not solve all test data constraints. "
                    + "Adjust the SMT solver settings (e.g. timeout) in Options->SMT Solvers.");
        }

        clazz.addMethod(getMainMethod(fileName, counter));

        if (isJunit()) {
            clazz.addMethods(oracleMethods);
        }

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
                KeYConstants.VERSION, fileName + ".java");
        return jfile.build();
    }

    public String inferSort(Map<String, Sort> typeInfMap, String progVar) {
        if (typeInfMap.containsKey(progVar)) {
            return typeInfMap.get(progVar).name().toString();
        }
        LOGGER.warn("Warning: inferSort did not find:  {}", progVar);
        return "NOTYPE";
    }

    public Map<String, Sort> generateTypeInferenceMap(Node n) {
        HashMap<String, Sort> typeInfMap = new HashMap<>();
        for (SequentFormula sequentFormula : n.sequent()) {
            Term t = sequentFormula.formula();
            generateTypeInferenceMapHelper(t, typeInfMap);
        }
        return typeInfMap;
    }

    private void generateTypeInferenceMapHelper(Term t, Map<String, Sort> map) {
        Operator op = t.op();
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
                if (pv == null) return;

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
        if (locationTerm.op() instanceof Function function) {
            // Make sure that the function is not an array
            if (heapLDT.getArr() != function) {
                String typeName = HeapLDT.getClassName(function);
                KeYJavaType type = services.getJavaInfo().getKeYJavaType(typeName);
                if (type != null) {
                    String fieldName = HeapLDT.getPrettyFieldName(function);
                    result = services.getJavaInfo().getAttribute(fieldName, type);
                }
            }
        }
        return result;
    }

    private String getRemainingConstants(Collection<String> existingConstants,
                                         Collection<Term> newConstants) {
        StringBuilder result = new StringBuilder();

        for (Term c : newConstants) {

            if (!existingConstants.contains(c.toString())) {

                String init = "null";
                if (c.sort().equals(services.getTypeConverter().getIntegerLDT().targetSort())) {
                    init = "0";
                } else if (c.sort()
                        .equals(services.getTypeConverter().getBooleanLDT().targetSort())) {
                    init = "false";
                }

                result.append(NEW_LINE).append(TAB).append(NULLABLE).append(" ")
                        .append(getSafeType(c.sort())).append(" ").append(c).append(" = ")
                        .append(init);
                if (isJunit()) {
                    result.append(NULLABLE)
                            .append(" ")
                            .append(getSafeType(c.sort())).append(" ")
                            .append(getPreName(c.toString())).append(" = ")
                            .append(init);
                }
            }
        }
        return result.toString();
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
                final String type = getSafeType(o.getSort());
                String right;
                if (type.endsWith("[]")) {
                    right =
                            "new " + type.substring(0, type.length() - 2) + "[" + o.getLength() + "]";
                } else if (o.getSort() == null || o.getSort().toString().equals("Null")) {
                    right = "null";
                } else {
                    if (settings.useRFL()) {
                        right = "RFL.new" + ReflectionClassCreator.cleanTypeName(type) + "()";
                        rflCreator.addSort(type);
                        LOGGER.debug("Adding sort (create Object): {}", type);
                    } else {
                        right = "new " + type + "()";
                    }
                }

                String objName = createObjectName(o);
                objects.add(objName);
                mb.addStatement(assignmentCreator.assign(type, objName, right));

                if (isJunit() && isInPrestate(prestate, o)) {
                    mb.addStatement(assignmentCreator.assign(type, getPreName(objName), right));
                }
            }
        }


        // init constants
        for (final String c : m.getConstants().keySet()) {
            String val = m.getConstants().get(c);
            if (filterVal(val) && !c.equals("null")) {
                boolean isObject = false;
                boolean isLiteral = false;
                String type = "int";
                String declType;
                if (val.equals("true") || val.equals("false")) {
                    type = "boolean";
                    isLiteral = true;
                } else if (StringUtil.isNumber(val)) {
                    isLiteral = true;
                } else if (val.startsWith("#o")) {
                    isObject = true;
                    type = this.inferSort(typeInfMap, c);
                }
                if (!type.equals("NOTYPE")) {
                    if (isObject) {
                        declType = NULLABLE + " " + type;
                    } else {
                        declType = type;
                    }
                    val = translateValueExpression(val);
                    mb.addStatement(assignmentCreator.assign(declType, c, "(" + type + ")" + val));


                    if (isJunit() && (isObject || Character.isJavaIdentifierStart(c.charAt(0)))
                            && isInPrestate(prestate, val)) {
                        if (isLiteral) {
                            mb.addStatement(assignmentCreator.assign(declType, getPreName(c),
                                    "(" + type + ")" + val));
                        } else {
                            mb.addStatement(assignmentCreator.assign(declType, getPreName(c),
                                    "(" + type + ")" + getPreName(val)));
                        }
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
                    final String vType = this.inferSort(typeInfMap, fieldName2);
                    // possible bug if vType represents an abstract type or an interface. See:
                    // getSafeType.
                    rflCreator.addSort(vType);

                    LOGGER.debug("Added sort (init fields): {}", vType);
                    val = translateValueExpression(val);
                    final String rcObjType = getSafeType(o.getSort());

                    mb.addStatement(assignmentCreator.assign("",
                            new RefEx(rcObjType, receiverObject, vType, fieldName),
                            "(" + vType + ")" + val));


                    if (isJunit() && isInPrestate(prestate, o)) {
                        // if value that is pointed to is object and in prestate then use prestate
                        // object
                        if (!vType.equals("int") && !vType.equals("boolean")
                                && isInPrestate(prestate, val) && !val.equals("null")) {
                            val = getPreName(val);
                        }

                        mb.addStatement(assignmentCreator.assign("",
                                new RefEx(rcObjType, getPreName(receiverObject), vType, fieldName),
                                "(" + vType + ")" + val));
                    }

                }
                if (o.getSort() != null && o.getSort().name().toString().endsWith("[]")) {

                    String safeType = getSafeType(o.getSort());
                    String elementType = safeType.substring(0, safeType.length() - 2);
                    rflCreator.addSort(safeType);
                    LOGGER.debug("Added sort (init array fields): {}", safeType);

                    for (int i = 0; i < o.getLength(); i++) {
                        final String fieldName = "[" + i + "]";
                        String val = o.getArrayValue(i);
                        val = translateValueExpression(val);
                        mb.addStatement(
                                assignmentCreator.assign("", receiverObject + fieldName, val));

                        if (isJunit() && isInPrestate(prestate, o)) {
                            if (!elementType.equals("int") && !elementType.equals("boolean")
                                    && isInPrestate(prestate, val) && !val.equals("null")) {
                                val = getPreName(val);
                            }
                            mb.addStatement(assignmentCreator.assign("",
                                    getPreName(receiverObject) + fieldName, val));
                        }
                    }
                }
            }
        }


        if (isJunit()) {
            createOldMap(mb, objects);
            createBoolSet(mb);
            createIntSet(mb);
            createObjSet(mb, heap);
        }
    }

    private void createOldMap(MethodSpec.Builder mb, Set<String> objNames) {
        ClassName NAME_HASH_MAP = ClassName.get(HashMap.class);
        var map =
                ParameterizedTypeName.get(NAME_HASH_MAP, ClassName.OBJECT, ClassName.OBJECT);
        mb.addStatement("$T $N = new $T()", map, OLDMap, map);
        for (String o : objNames) {
            mb.addStatement("$N.put($N, $L)", OLDMap, getPreName(o), o);
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

        /*
         * res.append(" public static void  main (java.lang.String[]  arg) {").append(NEW_LINE)
         * .append("   ").append(className).append(" testSuiteObject;").append(NEW_LINE)
         * .append("   testSuiteObject=new ").append(className).append(" ();").append(NEW_LINE)
         * .append(NEW_LINE);
         * for (int j = 0; j < i; j++) {
         * res.append("   testSuiteObject.testcode").append(j).append("();").append(NEW_LINE);
         * }
         * if (i == 0) {
         * res.append("   //Warning:no test methods were generated.").append(NEW_LINE);
         * }
         * res.append(" }");
         */

        var clazz = TypeSpec.classBuilder(className);
        clazz.addMethod(main);
        return main;
    }

    private void createBoolSet(MethodSpec.Builder mb) {
        // bool
        var SET_NAME = ClassName.get(HashSet.class);
        var BOOL_SET = ParameterizedTypeName.get(SET_NAME, TypeName.BOOLEAN);
        mb.addStatement("$T $N = new $T();", BOOL_SET, ALL_BOOLS, BOOL_SET);
        mb.addStatement("$N.add($L);", ALL_BOOLS, true);
        mb.addStatement("$N.add($L);", ALL_BOOLS, false);
    }

    private static void createIntSet(MethodSpec.Builder mb) {
        long size = ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings().getIntBound();
        long low = (long) -Math.pow(2, size - 1);
        long hi = (long) (Math.pow(2, size - 1) - 1);

        var SET_NAME = ClassName.get(HashSet.class);
        var SET_INT = ParameterizedTypeName.get(SET_NAME, TypeName.INT.box());

        mb.addStatement("$T $N = new $T();", SET_INT, ALL_INTS, SET_INT);
        for (long i = low; i <= hi; i++) {
            mb.addStatement("$N.add($L);", ALL_INTS, i);
        }
    }

    private void createObjSet(MethodSpec.Builder mb, Heap h) {
        var SET_NAME = ClassName.get(HashSet.class);
        var BOOL_SET = ParameterizedTypeName.get(SET_NAME, TypeName.OBJECT);
        mb.addStatement("$T $N = new $T();", BOOL_SET, ALL_OBJECTS, BOOL_SET);

        for (ObjectVal o : h.getObjects()) {
            String name = o.getName();
            if (name.equals("#o0")) {
                continue;
            }
            name = name.replace("#", "_");
            mb.addStatement("$N.add($N);", ALL_OBJECTS, name);
        }
    }

    public String getSafeType(Sort sort) {
        if (sort.name().toString().equals("Null")) {
            return "java.lang.Object";
        } else if (sort.isAbstract()) {
            return buildDummyClassForAbstractSort(sort);
        } else {
            return sort.name().toString();
        }
    }

    public boolean isJunit() {
        return settings.useJunit() == JUnit4 || settings.useJunit() == Format.JUnit5;
    }
}
