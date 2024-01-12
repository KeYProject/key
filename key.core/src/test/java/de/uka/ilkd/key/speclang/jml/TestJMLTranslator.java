/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml;

import java.io.File;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.speclang.njml.JmlIO;
import de.uka.ilkd.key.speclang.njml.SpecMathMode;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static java.lang.String.format;
import static org.junit.jupiter.api.Assertions.*;


public class TestJMLTranslator {
    public static final String testFile = HelperClassForTests.TESTCASE_DIRECTORY + File.separator
        + "speclang" + File.separator + "testFile.key";
    private static TermBuilder TB;
    private static JavaInfo javaInfo;
    private static Services services;
    private static KeYJavaType testClassType;
    private static final Map<LocationVariable, Term> atPres = new LinkedHashMap<>();
    private JmlIO jmlIO;


    @BeforeEach
    public synchronized void setUp() {
        if (javaInfo == null) {
            javaInfo =
                new HelperClassForTests().parse(new File(testFile)).getFirstProof().getJavaInfo();
            services = javaInfo.getServices();
            TB = services.getTermBuilder();
            testClassType = javaInfo.getKeYJavaType("testPackage.TestClass");
            atPres.put(services.getTypeConverter().getHeapLDT().getHeap(),
                TB.var(TB.heapAtPreVar("heapAtPre", false)));
        }
        jmlIO = new JmlIO().services(services).classType(testClassType)
                .specMathMode(JMLInfoExtractor.getSpecMathModeOrDefault(testClassType))
                .selfVar(buildSelfVarAsProgVar());
    }

    protected ProgramVariable buildSelfVarAsProgVar() {
        ProgramElementName classPEN = new ProgramElementName("self");
        return new LocationVariable(classPEN, testClassType);
    }


    protected ProgramVariable buildExcVar() {
        KeYJavaType excType = javaInfo.getTypeByClassName("java.lang.Throwable");
        ProgramElementName excPEN = new ProgramElementName("exc");
        return new LocationVariable(excPEN, excType);
    }


    protected ProgramVariable buildResultVar(IProgramMethod pm) {
        ProgramElementName resPEN = new ProgramElementName("result");
        return new LocationVariable(resPEN, pm.getReturnType());
    }


    private boolean termContains(Term t, Term sub) {

        for (int i = 0; i < t.arity(); i++) {
            if (t.sub(i).equals(sub) || termContains(t.sub(i), sub)) {
                return true;
            }
        }

        return false;
    }


    private boolean termContains(Term t, Operator op) {

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
        Term result = jmlIO.parseExpression("true");
        assertNotNull(result);
        assertEquals(result, TB.tt());
    }


    @Test
    public void testSelfVar() {
        ProgramVariable selfVar = buildSelfVarAsProgVar();
        Term result = jmlIO.selfVar(selfVar).parseExpression("this");
        assertNotNull(result);
        assertEquals(result, TB.var(selfVar));
    }


    @Test
    public void testLogicalExpression() {
        ProgramVariable selfVar = buildSelfVarAsProgVar();
        Term result = jmlIO.parseExpression("(b <= s &&  i > 5) ==> this != instance");
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
        ProgramVariable var = new LocationVariable(classPEN, testClassType);
        jmlIO.parameters(ImmutableSLList.singleton(var)).parseExpression("(o.i)");
    }

    @Test
    public void testPrimitiveField() {
        ProgramVariable selfVar = buildSelfVarAsProgVar();
        Term result = jmlIO.parseExpression("this.i");
        assertNotNull(result);
        assertTrue(termContains(result, selfVar));
    }

    @Test
    public void testSimpleQuery() {
        ProgramVariable selfVar = buildSelfVarAsProgVar();
        IProgramMethod getOne = javaInfo.getProgramMethod(testClassType, "getOne",
            ImmutableSLList.<KeYJavaType>nil(), testClassType);
        Term result = jmlIO.parseExpression("this.getOne()");
        assertNotNull(result);
        assertTrue(termContains(result, selfVar));
        assertTrue(termContains(result, getOne));
    }


    @Test
    public void testForAll() {
        Term result = jmlIO.parseExpression("(\\forall int i; (0 <= i && i <= 2147483647) )");

        assertNotNull(result);
        assertEquals(Quantifier.ALL, result.op());
        assertTrue(termContains(result, TB.zTerm("2147483647")));
        assertTrue(termContains(result, Junctor.AND));
        LogicVariable i = new LogicVariable(new Name("i"),
            services.getNamespaces().sorts().lookup(new Name("int")));
        Term expected = TB.all(i, TB.imp(TB.inInt(TB.var(i)),
            TB.and(TB.leq(TB.zTerm("0"), TB.var(i)), TB.leq(TB.var(i), TB.zTerm("2147483647")))));
        assertTrue(result.equalsModRenaming(expected),
            "Result was: " + result + "; \nExpected was: " + expected);
    }


    @Test
    public void testForEx() {
        Term result = jmlIO.parseExpression("(\\exists int i; (0 <= i && i <= 2147483647) )");
        assertNotNull(result);
        assertEquals(Quantifier.EX, result.op());
        assertTrue(termContains(result, TB.zTerm("2147483647")));
        assertTrue(termContains(result, Junctor.AND));
        LogicVariable i = new LogicVariable(new Name("i"),
            services.getNamespaces().sorts().lookup(new Name("int")));
        Term expected = TB.ex(i, TB.and(TB.inInt(TB.var(i)),
            TB.and(TB.leq(TB.zTerm("0"), TB.var(i)), TB.leq(TB.var(i), TB.zTerm("2147483647")))));
        assertTrue(result.equalsModRenaming(expected),
            "Result was: " + result + "; \nExpected was: " + expected);
    }


    @Test
    public void testBsumInt() {
        jmlIO.specMathMode(SpecMathMode.JAVA);
        Term result = jmlIO.parseExpression("(\\bsum int i; 0; 2147483647; i)");
        NamespaceSet nss = services.getNamespaces();
        Function q = nss.functions().lookup(new Name("bsum"));
        LogicVariable i = new LogicVariable(new Name("i"), nss.sorts().lookup(new Name("int")));
        Term expected = TB.func(services.getTypeConverter().getIntegerLDT().getModuloInt(),
            TB.bsum(i, TB.zTerm("0"), TB.zTerm("2147483647"), TB.var(i)));
        assertNotNull(result);
        Assertions.assertSame(q, result.sub(0).op());
        assertTrue(result.equalsModRenaming(expected),
            "Result was: " + result + "; \nExpected was: " + expected);
    }


    @Test
    public void testBsumBigInt() {
        Term result = jmlIO.parseExpression("(\\bsum \\bigint i; 0; 2147483647; i)");
        NamespaceSet nss = services.getNamespaces();
        Function q = nss.functions().lookup(new Name("bsum"));
        LogicVariable i = new LogicVariable(new Name("i"), nss.sorts().lookup(new Name("int")));
        Term expected = TB.bsum(i, TB.zTerm("0"), TB.zTerm("2147483647"), TB.var(i));
        assertNotNull(result);
        Assertions.assertSame(q, result.op());
        assertTrue(result.equalsModRenaming(expected),
            "Result was: " + result + "; \nExpected was: " + expected);
    }

    @Test
    public void testInfiniteUnion() {
        final String input = "\\infinite_union(Object o; \\empty)";
        Term result = jmlIO.parseExpression(input);
        assertNotNull(result);
        Operator unionOp = services.getTypeConverter().getLocSetLDT().getInfiniteUnion();
        LogicVariable o =
            new LogicVariable(new Name("o"), services.getJavaInfo().getJavaLangObject().getSort());
        Assertions.assertSame(unionOp, result.op());
        Term guard = TB.and(TB.convertToFormula(TB.created(TB.var(o))),
            TB.not(TB.equals(TB.var(o), TB.NULL())));
        Term expected = TB.infiniteUnion(new QuantifiableVariable[] { o },
            TB.ife(guard, TB.empty(), TB.empty()));
        assertTrue(result.equalsModRenaming(expected),
            "Result was: " + result + "; \nExpected was: " + expected);
    }

    @Test
    public void testInfiniteUnion2() {
        // weigl: adapt to new syntax
        final String input = "(\\infinite_union nullable Object o; \\empty)";
        Term result = jmlIO.parseExpression(input);
        assertNotNull(result);
        Operator unionOp = services.getTypeConverter().getLocSetLDT().getInfiniteUnion();
        LogicVariable o =
            new LogicVariable(new Name("o"), services.getJavaInfo().getJavaLangObject().getSort());
        Assertions.assertSame(unionOp, result.op());
        Term guard =
            TB.or(TB.convertToFormula(TB.created(TB.var(o))), TB.equals(TB.var(o), TB.NULL()));
        Term expected = TB.infiniteUnion(new QuantifiableVariable[] { o },
            TB.ife(guard, TB.empty(), TB.empty()));
        assertTrue(result.equalsModRenaming(expected),
            "Result was: " + result + "; \nExpected was: " + expected);
    }


    @Test
    public void testComplexExists() {
        Term result = jmlIO.parseExpression("(\\exists TestClass t; t != null; t.i == 0)");
        assertNotNull(result);
        assertEquals(Quantifier.EX, result.op());
        assertEquals(Junctor.AND, result.sub(0).op());
        assertTrue(termContains(result, TB.NULL()));
    }

    @Test
    public void testOld() {
        ProgramVariable excVar = buildExcVar();

        Term result = jmlIO.exceptionVariable(excVar).atPres(atPres)
                .parseExpression("this.i == \\old(this.i)");

        assertNotNull(result);
        assertEquals(Equality.EQUALS, result.op());
        assertTrue(termContains(result, services.getTypeConverter().getHeapLDT().getHeap()));
        assertTrue(termContains(result,
            atPres.get(services.getTypeConverter().getHeapLDT().getHeap()).op()));
    }

    @Test
    public void testResultVar() {
        ProgramVariable excVar = buildExcVar();

        ImmutableList<KeYJavaType> signature = ImmutableSLList.nil();

        IProgramMethod pm =
            javaInfo.getProgramMethod(testClassType, "getOne", signature, testClassType);

        ProgramVariable resultVar = buildResultVar(pm);

        Term result = jmlIO.atPres(atPres).resultVariable(resultVar).exceptionVariable(excVar)
                .parseExpression("\\result == 1");

        assertNotNull(result);
        assertEquals(Equality.EQUALS, result.op());
        assertTrue(termContains(result, resultVar));

    }


    @Test
    public void testNonNullElements() {

        Term result = jmlIO.atPres(atPres).parseExpression("\\nonnullelements(this.array)");

        assertNotNull(result);
        assertTrue(termContains(result, TB.NULL()));
    }


    @Test
    public void testIsInitialized() {
        Term result =
            jmlIO.atPres(atPres).parseExpression("\\is_initialized(testPackage.TestClass)");
        assertNotNull(result);
        assertEquals(Equality.EQUALS, result.op());
        assertTrue(termContains(result, TB.var(
            javaInfo.getAttribute(ImplicitFieldAdder.IMPLICIT_CLASS_INITIALIZED, testClassType))));
    }

    @Test
    public void testHexLiteral() {
        Term result = jmlIO.parseExpression(" i == 0x12 ");
        assertNotNull(result);
        assertEquals(Equality.EQUALS, result.op());
        assertTrue(termContains(result, TB.zTerm("18")));
    }


    @Test
    public void testComplexQueryResolving1() {
        ImmutableList<KeYJavaType> signature = ImmutableSLList.nil();
        signature = signature.append(javaInfo.getKeYJavaType(PrimitiveType.JAVA_INT));

        IProgramMethod pm = javaInfo.getProgramMethod(testClassType, "m", signature, testClassType);

        Term result = jmlIO.parseExpression("this.m((int)4 + 2) == this.m(i)");

        assertNotNull(result);
        assertEquals(result.sub(0).op(), pm);
        assertEquals(result.sub(1).op(), pm);
    }


    @Test
    public void testComplexQueryResolving2() {
        ImmutableList<KeYJavaType> signature = ImmutableSLList.nil();
        signature = signature.append(javaInfo.getKeYJavaType(PrimitiveType.JAVA_LONG));

        IProgramMethod pm = javaInfo.getProgramMethod(testClassType, "m", signature, testClassType);

        Term result = jmlIO.parseExpression("this.m(l) == this.m((long)i + 3)");

        assertNotNull(result);
        assertEquals(result.sub(0).op(), pm);
        assertEquals(result.sub(1).op(), pm);
    }


    @Test
    public void testComplexQueryResolving3() {
        ImmutableList<KeYJavaType> signature = ImmutableSLList.nil();
        signature = signature.append(javaInfo.getKeYJavaType(PrimitiveType.JAVA_INT));

        IProgramMethod pm = javaInfo.getProgramMethod(testClassType, "m", signature, testClassType);

        Term result = jmlIO.parseExpression("this.m(s + 4) == this.m(+b)");

        assertNotNull(result);
        assertEquals(result.sub(0).op(), pm);
        assertEquals(result.sub(1).op(), pm);
    }


    @Test
    public void testStaticQueryResolving() {
        ImmutableList<KeYJavaType> signature = ImmutableSLList.nil();

        IProgramMethod pm =
            javaInfo.getProgramMethod(testClassType, "staticMethod", signature, testClassType);

        Term result = jmlIO.parseExpression("testPackage.TestClass.staticMethod() == 4");

        assertNotNull(result);
        assertEquals(result.sub(0).op(), pm);
    }


    @Test
    public void testSubtypeExpression() {
        Term resultTypeofClass = jmlIO.parseExpression(
            "( \\exists TestClass t; t != null; \\typeof(t) <: \\type(java.lang.Object) )");
        Term resultTypeofPrimitive =
            jmlIO.parseExpression("( \\exists int i; \\typeof(i) <: \\type(int) )");

        assertNotNull(resultTypeofClass);
        assertNotNull(resultTypeofPrimitive);

        Function ioFuncObject = javaInfo.objectSort().getInstanceofSymbol(services);
        Function ioFuncInt =
            services.getNamespaces().sorts().lookup("int").getInstanceofSymbol(services);

        assertTrue(termContains(resultTypeofClass, ioFuncObject));
        assertTrue(termContains(resultTypeofPrimitive, ioFuncInt));
    }


    @Test
    public void testCorrectImplicitThisResolution() {
        ProgramVariable selfVar = buildSelfVarAsProgVar();
        LocationVariable array =
            (LocationVariable) javaInfo.getAttribute("testPackage.TestClass::array");

        Term result = jmlIO.selfVar(selfVar)
                .parseExpression("(\\forall TestClass a;a.array == array; a == this)");

        assertNotNull(result);
        final LogicVariable qv = new LogicVariable(new Name("a"), selfVar.sort());
        final Function fieldSymbol =
            services.getTypeConverter().getHeapLDT().getFieldSymbolForPV(array, services);
        Term expected = TB.all(qv,
            TB.imp(
                TB.and(
                    TB.and(
                        TB.equals(TB.dot(array.sort(), TB.var(qv), fieldSymbol),
                            TB.dot(array.sort(), TB.var(selfVar), fieldSymbol)),
                        TB.reachableValue(TB.var(qv), selfVar.getKeYJavaType())),
                    TB.not(TB.equals(TB.var(qv), TB.NULL()))), // implicit non null
                TB.equals(TB.var(qv), TB.var(selfVar))));

        final boolean condition = result.equalsModRenaming(expected);
        assertTrue(condition, format("Expected:%s\n Was:%s",
            ProofSaver.printTerm(expected, services), ProofSaver.printTerm(result, services)));
    }

}
