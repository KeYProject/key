/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang.jml;

import java.nio.file.Path;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Objects;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.ast.reference.TypeRef;
import de.uka.ilkd.key.java.transformations.pipeline.PipelineConstants;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.speclang.njml.JmlIO;
import de.uka.ilkd.key.speclang.njml.SpecMathMode;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableList;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;

import static de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;
import static de.uka.ilkd.key.logic.equality.TermLabelsProperty.TERM_LABELS_PROPERTY;
import static java.lang.String.format;
import static org.junit.jupiter.api.Assertions.*;


public class TestJMLTranslator {
    public static final Path testFile = HelperClassForTests.TESTCASE_DIRECTORY
            .resolve("speclang").resolve("testFile.key");
    // assigned once in setUp(); JUnit-lifecycle assignment is invisible to NullAway's field
    // initialization analysis
    @SuppressWarnings("NullAway")
    private static TermBuilder TB;
    @SuppressWarnings("NullAway")
    private static JavaInfo javaInfo;
    @SuppressWarnings("NullAway")
    private static Services services;
    @SuppressWarnings("NullAway")
    private static KeYJavaType testClassType;
    private static final Map<LocationVariable, JTerm> atPres = new LinkedHashMap<>();
    private JmlIO jmlIO;


    @BeforeEach
    public synchronized void setUp() {
        if (javaInfo == null) {
            javaInfo = Objects
                    .requireNonNull(HelperClassForTests.parse(testFile).getFirstProof(),
                        "the test file must contain a proof")
                    .getJavaInfo();
            services = javaInfo.getServices();
            TB = services.getTermBuilder();
            testClassType = Objects.requireNonNull(
                javaInfo.getKeYJavaType("testPackage.TestClass"));

            var heapLDT = Objects
                    .requireNonNull(services.getTypeConverter().getHeapLDT(),
                        "the heap LDT must be available");
            atPres.put(heapLDT.getHeap(), TB.var(TB.heapAtPreVar("heapAtPre", false)));
        }
        jmlIO = new JmlIO(services).classType(testClassType)
                .specMathMode(JMLInfoExtractor.getSpecMathModeOrDefault(testClassType))
                .selfVar(buildSelfVarAsProgVar());
    }

    protected LocationVariable buildSelfVarAsProgVar() {
        ProgramElementName classPEN = new ProgramElementName("self");
        return new LocationVariable(classPEN, new TypeRef(testClassType));
    }


    protected LocationVariable buildExcVar() {
        KeYJavaType excType = Objects.requireNonNull(
            javaInfo.getTypeByClassName("java.lang.Throwable"), "the exception type must exist");
        ProgramElementName excPEN = new ProgramElementName("exc");
        return new LocationVariable(excPEN, new TypeRef(excType));
    }


    protected LocationVariable buildResultVar(IProgramMethod pm) {
        ProgramElementName resPEN = new ProgramElementName("result");
        return new LocationVariable(resPEN, new TypeRef(
            Objects.requireNonNull(pm.getReturnType(), "the method has a return type")));
    }


    private boolean termContains(JTerm t, JTerm sub) {
        for (int i = 0; i < t.arity(); i++) {
            if (t.sub(i).equals(sub) || termContains(t.sub(i), sub)) {
                return true;
            }
        }

        return false;
    }


    private boolean termContains(JTerm t, Operator op) {

        if (t.op().arity() == op.arity() && t.op().name().equals(op.name())) {
            return true;
        }

        for (int i = 0; i < t.arity(); i++) {
            if (termContains(t.sub(i), op)) {
                return true;
            }
        }

        return false;
    }

    @Test
    public void testTrueTerm() {
        JTerm result = jmlIO.parseExpression("true");
        assertNotNull(result);
        assertEquals(result, TB.tt());
    }


    @Test
    public void testSelfVar() {
        LocationVariable selfVar = buildSelfVarAsProgVar();
        JTerm result = jmlIO.selfVar(selfVar).parseExpression("this");
        assertNotNull(result);
        assertEquals(result, TB.var(selfVar));
    }


    @Test
    public void testLogicalExpression() {
        LocationVariable selfVar = buildSelfVarAsProgVar();
        JTerm result = jmlIO.parseExpression("(b <= s &&  i > 5) ==> this != instance");
        assertNotNull(result);
        assertEquals(Junctor.IMP, result.op());
        assertEquals(Junctor.AND, result.sub(0).op());
        assertTrue(termContains(result, TB.zTerm("5")));
        assertTrue(termContains(result, selfVar));
    }

    // There is a problem with spaces here.
    // Adding spaces around "j < i" solves the problem.
    // see bug MT-1548
    @Test
    public void testSumParsing() {
        jmlIO.parseExpression("0 == ((\\sum int j; 0<=j && j<i; j))");
    }

    // see bug #1528
    @Test
    public void testParenExpression() {
        ProgramElementName classPEN = new ProgramElementName("o");
        LocationVariable var = new LocationVariable(classPEN, new TypeRef(testClassType));
        jmlIO.parameters(ImmutableList.singleton(var)).parseExpression("(o.i)");
    }

    @Test
    public void testPrimitiveField() {
        ProgramVariable selfVar = buildSelfVarAsProgVar();
        JTerm result = jmlIO.parseExpression("this.i");
        assertNotNull(result);
        assertTrue(termContains(result, selfVar));
    }

    @Test
    public void testSimpleQuery() {
        ProgramVariable selfVar = buildSelfVarAsProgVar();
        IProgramMethod getOne = Objects
                .requireNonNull(
                    javaInfo.getProgramMethod(testClassType, "getOne", ImmutableList.nil(),
                        testClassType),
                    "the method must exist");
        JTerm result = jmlIO.parseExpression("this.getOne()");
        assertNotNull(result);
        assertTrue(termContains(result, selfVar));
        assertTrue(termContains(result, getOne));
    }


    @Test
    public void testForAll() {
        JTerm result = jmlIO.parseExpression("(\\forall int i; (0 <= i && i <= 2147483647) )");

        assertNotNull(result);
        assertEquals(Quantifier.ALL, result.op());
        assertTrue(termContains(result, TB.zTerm("2147483647")));
        assertTrue(termContains(result, Junctor.AND));
        Sort intSort = Objects
                .requireNonNull(services.getNamespaces().sorts().lookup(new Name("int")),
                    "the int sort exists");
        LogicVariable i = new LogicVariable(new Name("i"), intSort);
        JTerm expected = TB.all(i, TB.imp(TB.inInt(TB.var(i)),
            TB.and(TB.leq(TB.zTerm("0"), TB.var(i)), TB.leq(TB.var(i), TB.zTerm("2147483647")))));
        assertTrue(RENAMING_TERM_PROPERTY.equalsModThisProperty(result, expected),
            "Result was: " + result + "; \nExpected was: " + expected);
        assertEquals(result.hashCodeModProperty(RENAMING_TERM_PROPERTY),
            expected.hashCodeModProperty(RENAMING_TERM_PROPERTY),
            "Hash codes should be equal modulo renaming.");
    }


    @Test
    public void testForEx() {
        JTerm result = jmlIO.parseExpression("(\\exists int i; (0 <= i && i <= 2147483647) )");
        assertNotNull(result);
        assertEquals(Quantifier.EX, result.op());
        assertTrue(termContains(result, TB.zTerm("2147483647")));
        assertTrue(termContains(result, Junctor.AND));
        Sort intSort = Objects
                .requireNonNull(services.getNamespaces().sorts().lookup(new Name("int")),
                    "the int sort exists");
        LogicVariable i = new LogicVariable(new Name("i"), intSort);
        JTerm expected = TB.ex(i, TB.and(TB.inInt(TB.var(i)),
            TB.and(TB.leq(TB.zTerm("0"), TB.var(i)), TB.leq(TB.var(i), TB.zTerm("2147483647")))));
        assertTrue(RENAMING_TERM_PROPERTY.equalsModThisProperty(result, expected),
            "Result was: " + result + "; \nExpected was: " + expected);
        assertEquals(result.hashCodeModProperty(RENAMING_TERM_PROPERTY),
            expected.hashCodeModProperty(RENAMING_TERM_PROPERTY),
            "Hash codes should be equal modulo renaming.");
    }


    @Test
    public void testBsumInt() {
        jmlIO.specMathMode(SpecMathMode.JAVA);
        JTerm result = jmlIO.parseExpression("(\\bsum int i; 0; 2147483647; i)");
        NamespaceSet nss = services.getNamespaces();
        Function q = nss.functions().lookup(new Name("bsum"));
        Sort intSort = Objects
                .requireNonNull(nss.sorts().lookup(new Name("int")), "the int sort exists");
        LogicVariable i = new LogicVariable(new Name("i"), intSort);
        JTerm expected = TB.func(services.getTypeConverter().getIntegerLDT().getModuloInt(),
            TB.bsum(i, TB.zTerm("0"), TB.zTerm("2147483647"), TB.var(i)));
        assertNotNull(result);
        assertSame(q, result.sub(0).op());
        assertTrue(RENAMING_TERM_PROPERTY.equalsModThisProperty(result, expected),
            "Result was: " + result + "; \nExpected was: " + expected);
        assertEquals(result.hashCodeModProperty(RENAMING_TERM_PROPERTY),
            expected.hashCodeModProperty(RENAMING_TERM_PROPERTY),
            "Hash codes should be equal modulo renaming.");
    }


    @Test
    public void testBsumBigInt() {
        JTerm result = jmlIO.parseExpression("(\\bsum \\bigint i; 0; 2147483647; i)");
        NamespaceSet nss = services.getNamespaces();
        Function q = nss.functions().lookup(new Name("bsum"));
        Sort intSort = Objects
                .requireNonNull(nss.sorts().lookup(new Name("int")), "the int sort exists");
        LogicVariable i = new LogicVariable(new Name("i"), intSort);
        JTerm expected = TB.bsum(i, TB.zTerm("0"), TB.zTerm("2147483647"), TB.var(i));
        assertNotNull(result);
        assertSame(q, result.op());
        assertTrue(RENAMING_TERM_PROPERTY.equalsModThisProperty(result, expected),
            "Result was: " + result + "; \nExpected was: " + expected);
        assertEquals(result.hashCodeModProperty(RENAMING_TERM_PROPERTY),
            expected.hashCodeModProperty(RENAMING_TERM_PROPERTY),
            "Hash codes should be equal modulo renaming.");
    }

    @Test
    public void testInfiniteUnion() {
        final String input = "\\infinite_union(Object o; \\empty)";
        JTerm result = jmlIO.parseExpression(input);
        assertNotNull(result);
        Operator unionOp = services.getTypeConverter().getLocSetLDT().getInfiniteUnion();
        Sort objectSort =
            Objects.requireNonNull(services.getJavaInfo().getJavaLangObject().getSort(),
                "the object sort exists");
        LogicVariable o = new LogicVariable(new Name("o"), objectSort);
        assertSame(unionOp, result.op());
        JTerm guard = TB.and(TB.convertToFormula(TB.created(TB.var(o))),
            TB.not(TB.equals(TB.var(o), TB.NULL())));
        JTerm expected = TB.infiniteUnion(new QuantifiableVariable[] { o },
            TB.ife(guard, TB.empty(), TB.empty()));
        assertTrue(RENAMING_TERM_PROPERTY.equalsModThisProperty(result, expected),
            "Result was: " + result + "; \nExpected was: " + expected);
        assertEquals(result.hashCodeModProperty(RENAMING_TERM_PROPERTY),
            expected.hashCodeModProperty(RENAMING_TERM_PROPERTY),
            "Hash codes should be equal modulo renaming.");
    }

    @Test
    public void testInfiniteUnion2() {
        // weigl: adapt to new syntax
        final String input = "(\\infinite_union nullable Object o; \\empty)";
        JTerm result = jmlIO.parseExpression(input);
        assertNotNull(result);
        Operator unionOp = services.getTypeConverter().getLocSetLDT().getInfiniteUnion();
        Sort objectSort =
            Objects.requireNonNull(services.getJavaInfo().getJavaLangObject().getSort(),
                "the object sort exists");
        LogicVariable o = new LogicVariable(new Name("o"), objectSort);
        assertSame(unionOp, result.op());
        JTerm guard =
            TB.or(TB.convertToFormula(TB.created(TB.var(o))), TB.equals(TB.var(o), TB.NULL()));
        JTerm expected = TB.infiniteUnion(new QuantifiableVariable[] { o },
            TB.ife(guard, TB.empty(), TB.empty()));
        assertTrue(RENAMING_TERM_PROPERTY.equalsModThisProperty(result, expected),
            "Result was: " + result + "; \nExpected was: " + expected);
        assertEquals(result.hashCodeModProperty(RENAMING_TERM_PROPERTY),
            expected.hashCodeModProperty(RENAMING_TERM_PROPERTY),
            "Hash codes should be equal modulo renaming.");
    }


    @Test
    public void testComplexExists() {
        JTerm result = jmlIO.parseExpression("(\\exists TestClass t; t != null; t.i == 0)");
        assertNotNull(result);
        assertEquals(Quantifier.EX, result.op());
        assertEquals(Junctor.AND, result.sub(0).op());
        assertTrue(termContains(result, TB.NULL()));
    }

    @Test
    public void testOld() {
        LocationVariable excVar = buildExcVar();

        JTerm result = jmlIO.exceptionVariable(excVar).atPres(atPres)
                .parseExpression("this.i == \\old(this.i)");

        assertNotNull(result);
        assertEquals(Equality.EQUALS, result.op());
        var heapLDT = Objects
                .requireNonNull(services.getTypeConverter().getHeapLDT(),
                    "the heap LDT must be available");
        assertTrue(termContains(result, heapLDT.getHeap()));
        assertTrue(termContains(result,
            Objects
                    .requireNonNull(atPres.get(heapLDT.getHeap()),
                        "the pre-heap must be registered")
                    .op()));
    }

    @Test
    public void testResultVar() {
        LocationVariable excVar = buildExcVar();

        ImmutableList<KeYJavaType> signature = ImmutableList.nil();

        IProgramMethod pm = Objects
                .requireNonNull(
                    javaInfo.getProgramMethod(testClassType, "getOne", signature, testClassType),
                    "the method must exist");

        LocationVariable resultVar = buildResultVar(pm);

        JTerm result = jmlIO.atPres(atPres).resultVariable(resultVar).exceptionVariable(excVar)
                .parseExpression("\\result == 1");

        assertNotNull(result);
        assertEquals(Equality.EQUALS, result.op());
        assertTrue(termContains(result, resultVar));

    }


    @Test
    public void testNonNullElements() {

        JTerm result = jmlIO.atPres(atPres).parseExpression("\\nonnullelements(this.array)");

        assertNotNull(result);
        assertTrue(termContains(result, TB.NULL()));
    }


    @Test
    public void testIsInitialized() {
        JTerm result =
            jmlIO.atPres(atPres).parseExpression("\\is_initialized(testPackage.TestClass)");
        assertNotNull(result);
        assertEquals(Equality.EQUALS, result.op());
        ProgramVariable clsVar = Objects
                .requireNonNull(
                    javaInfo.getAttribute(PipelineConstants.IMPLICIT_CLASS_INITIALIZED,
                        testClassType),
                    "the implicit class initialization attribute must exist");
        assertTrue(termContains(result, TB.var(clsVar)));
    }

    @Test
    public void testHexLiteral() {
        JTerm result = jmlIO.parseExpression(" i == 0x12 ");
        assertNotNull(result);
        assertEquals(Equality.EQUALS, result.op());
        assertTrue(termContains(result, TB.zTerm("18")));
    }


    @Test
    public void testComplexQueryResolving1() {
        ImmutableList<KeYJavaType> signature = ImmutableList.nil();
        signature = signature.append(
            Objects.requireNonNull(javaInfo.getKeYJavaType(PrimitiveType.JAVA_INT),
                "the int type must exist"));

        IProgramMethod pm = javaInfo.getProgramMethod(testClassType, "m", signature, testClassType);

        JTerm result = jmlIO.parseExpression("this.m((int)4 + 2) == this.m(i)");

        assertNotNull(result);
        assertEquals(result.sub(0).op(), pm);
        assertEquals(result.sub(1).op(), pm);
    }


    @Test
    public void testComplexQueryResolving2() {
        ImmutableList<KeYJavaType> signature = ImmutableList.nil();
        signature = signature.append(
            Objects.requireNonNull(javaInfo.getKeYJavaType(PrimitiveType.JAVA_LONG),
                "the long type must exist"));

        IProgramMethod pm = javaInfo.getProgramMethod(testClassType, "m", signature, testClassType);

        JTerm result = jmlIO.parseExpression("this.m(l) == this.m((long)i + 3)");

        assertNotNull(result);
        assertEquals(result.sub(0).op(), pm);
        assertEquals(result.sub(1).op(), pm);
    }


    @Test
    public void testComplexQueryResolving3() {
        ImmutableList<KeYJavaType> signature = ImmutableList.nil();
        signature = signature.append(
            Objects.requireNonNull(javaInfo.getKeYJavaType(PrimitiveType.JAVA_INT),
                "the int type must exist"));

        IProgramMethod pm = javaInfo.getProgramMethod(testClassType, "m", signature, testClassType);

        JTerm result = jmlIO.parseExpression("this.m(s + 4) == this.m(+b)");

        assertNotNull(result);
        assertEquals(result.sub(0).op(), pm);
        assertEquals(result.sub(1).op(), pm);
    }


    @Test
    public void testStaticQueryResolving() {
        ImmutableList<KeYJavaType> signature = ImmutableList.nil();

        IProgramMethod pm =
            javaInfo.getProgramMethod(testClassType, "staticMethod", signature, testClassType);

        JTerm result = jmlIO.parseExpression("testPackage.TestClass.staticMethod() == 4");

        assertNotNull(result);
        assertEquals(result.sub(0).op(), pm);
    }


    @Test
    public void testSubtypeExpression() {
        JTerm resultTypeofClass = jmlIO.parseExpression(
            "( \\exists TestClass t; t != null; \\typeof(t) <: \\type(java.lang.Object) )");
        JTerm resultTypeofPrimitive =
            jmlIO.parseExpression("( \\exists int i; \\typeof(i) <: \\type(int) )");

        assertNotNull(resultTypeofClass);
        assertNotNull(resultTypeofPrimitive);

        Sort intSort =
            Objects.requireNonNull(services.getNamespaces().sorts().lookup("int"),
                "the int sort exists");
        Function ioFuncObject =
            services.getJavaDLTheory().getInstanceofSymbol(javaInfo.objectSort(), services);
        Function ioFuncInt = services.getJavaDLTheory().getInstanceofSymbol(intSort, services);

        assertTrue(termContains(resultTypeofClass, ioFuncObject));
        assertTrue(termContains(resultTypeofPrimitive, ioFuncInt));
    }


    @Test
    public void testCorrectImplicitThisResolution() {
        LocationVariable selfVar = buildSelfVarAsProgVar();
        LocationVariable array = Objects.requireNonNull(
            (LocationVariable) javaInfo.getAttribute("testPackage.TestClass::array"),
            "the array field must exist");

        JTerm result = jmlIO.selfVar(selfVar)
                .parseExpression("(\\forall TestClass a;a.array == array; a == this)");

        assertNotNull(result);
        final LogicVariable qv = new LogicVariable(new Name("a"), selfVar.sort());
        final Function fieldSymbol = Objects
                .requireNonNull(services.getTypeConverter().getHeapLDT(),
                    "the heap LDT must be available")
                .getFieldSymbolForPV(array, services);
        JTerm expected = TB.all(qv,
            TB.imp(
                TB.and(
                    TB.and(
                        TB.equals(TB.dot(array.sort(), TB.var(qv), fieldSymbol),
                            TB.dot(array.sort(), TB.var(selfVar), fieldSymbol)),
                        TB.reachableValue(TB.var(qv),
                            Objects.requireNonNull(selfVar.getKeYJavaType(),
                                "the self variable has a type"))),
                    TB.not(TB.equals(TB.var(qv), TB.NULL()))), // implicit non null
                TB.equals(TB.var(qv), TB.var(selfVar))));

        final boolean condition = RENAMING_TERM_PROPERTY.equalsModThisProperty(result, expected);
        assertTrue(condition, format("Expected:%s\n Was:%s",
            ProofSaver.printTerm(expected, services), ProofSaver.printTerm(result, services)));
    }

    @ParameterizedTest
    @CsvSource(value = {
        "\\seq(1) + \\seq(2,3) : \\seq_concat(\\seq(1), \\seq(2,3))",
        "\\locset(this.b) + \\locset(this.s) : \\set_union(\\locset(this.b), \\locset(this.s))",
        "\\locset(this.b) | \\locset(this.s) : \\set_union(\\locset(this.b), \\locset(this.s))",
        "\\locset(this.b) & \\locset(this.s) : \\intersect(\\locset(this.b), \\locset(this.s))",
        "\\locset(this.b) * \\locset(this.s) : \\intersect(\\locset(this.b), \\locset(this.s))",
        "\\locset(this.b) <= \\locset(this.s) : \\subset(\\locset(this.b), \\locset(this.s))",
        "\\locset(this.b) < \\locset(this.s) : \\subset(\\locset(this.b), \\locset(this.s)) && \\locset(this.b) != \\locset(this.s)",
        "\\locset(this.b) >= \\locset(this.s) : \\subset(\\locset(this.s), \\locset(this.b))",
        "\\locset(this.b) > \\locset(this.s) : \\subset(\\locset(this.s), \\locset(this.b)) && \\locset(this.b) != \\locset(this.s)",
    }, delimiter = ':')
    public void testOperatorOverloading(String expression, String expected) {
        JTerm tTrans = null, tExp = null;
        try {
            tTrans = jmlIO.parseExpression(expression);
        } catch (Exception e) {
            fail("Cannot parse " + expression, e);
        }

        try {
            tExp = jmlIO.parseExpression(expected);
        } catch (Exception e) {
            fail("Cannot parse " + expected, e);
        }

        if (!TERM_LABELS_PROPERTY.equalsModThisProperty(tTrans, tExp)) {
            // this gives nicer error
            assertEquals(tExp, tTrans);
        }
    }

}
