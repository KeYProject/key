// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package de.uka.ilkd.key.speclang.jml.translation;

import java.io.File;
import java.util.LinkedHashMap;
import java.util.Map;

import junit.framework.TestCase;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.util.HelperClassForTests;



public class TestJMLTranslator extends TestCase {

    public static final String testFile = System.getProperty("key.home")
                                          + File.separator + "examples"
                                          + File.separator + "_testcase"
                                          + File.separator + "speclang"
                                          + File.separator + "testFile.key";
    private static final TermBuilder TB = TermBuilder.DF;
    private static JavaInfo javaInfo;
    private static Services services;
    private static KeYJavaType testClassType;
    private static Map<LocationVariable,Term> atPres = new LinkedHashMap<LocationVariable,Term>();


    protected void setUp() {
        if (javaInfo != null) {
            return;
        }
        javaInfo = new HelperClassForTests().parse(
                new File(testFile)).getFirstProof().getJavaInfo();
        services = javaInfo.getServices();
        testClassType = javaInfo.getKeYJavaType("testPackage.TestClass");
        atPres.put(services.getTypeConverter().getHeapLDT().getHeap(), TB.var(TB.heapAtPreVar(services, "heapAtPre",
          services.getTypeConverter().getHeapLDT().getHeap().sort(), false)));
    }


    protected void tearDown() {
    }


    protected ProgramVariable buildSelfVarAsProgVar() {
        ProgramElementName classPEN = new ProgramElementName("self");
        ProgramVariable result = new LocationVariable(classPEN, testClassType);
        return result;
    }


    protected ProgramVariable buildExcVar() {
        KeYJavaType excType = javaInfo.getTypeByClassName("java.lang.Throwable");
        ProgramElementName excPEN = new ProgramElementName("exc");
        return new LocationVariable(excPEN, excType);
    }


    protected ProgramVariable buildResultVar(IProgramMethod pm) {
        ProgramElementName resPEN = new ProgramElementName("result");
        ProgramVariable result = new LocationVariable(resPEN,
                                                      pm.getReturnType());
        return result;
    }


    private boolean termContains(Term t,
                                 Term sub) {

        for (int i = 0; i < t.arity(); i++) {
            if (t.sub(i).equals(sub) || termContains(t.sub(i), sub)) {
                return true;
            }
        }

        return false;
    }


    private boolean termContains(Term t,
                                 Operator op) {

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


    public void testTrueTerm() {
        Term result = null;

        try {
            result = JMLTranslator.translate(new PositionedString("true"),
                                             testClassType, null, null, null,
                                             null, null, Term.class,
                                             services);
        } catch (SLTranslationException e) {
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.equals(TB.tt()));
    }


    public void testSelfVar() {
        Term result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();

        try {
            result = JMLTranslator.translate(new PositionedString("this"),
                                             testClassType, selfVar, null, null,
                                             null, null, Term.class,
                                             services);
        } catch (SLTranslationException e) {
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.equals(TB.var(selfVar)));
    }


    public void testLogicalExpression() {
        Term result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();

        try {
            result = JMLTranslator.translate(new PositionedString(
                    "(b <= s &&  i > 5) ==> this != instance"), testClassType,
                                                    selfVar, null, null, null,
                                                    null, Term.class, services);
        } catch (SLTranslationException e) {
            e.printStackTrace();
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.op().equals(Junctor.IMP));
        assertTrue(result.sub(0).op().equals(Junctor.AND));
        assertTrue(termContains(result, TB.zTerm(services, "5")));
        assertTrue(termContains(result, selfVar));
    }


    public void testPrimitiveField() {
        Term result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();
        ProgramVariable i = javaInfo.getAttribute("testPackage.TestClass::i");

        try {
            result = JMLTranslator.translate(new PositionedString(
                    "this.i"), testClassType,
                                             selfVar, null, null, null,
                                             null, Term.class, services);
        } catch (SLTranslationException e) {
            assertTrue(false);
        }

        assertTrue(result != null);
        //assertTrue(termContains(result.getFormula(), AttributeOp.getAttributeOp(i) ));
        assertTrue(termContains(result, selfVar));
    }


    public void testSimpleQuery() {
        Term result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();
        IProgramMethod getOne = javaInfo.getProgramMethod(testClassType,
                                                         "getOne",
                                                         ImmutableSLList.<KeYJavaType>nil(),
                                                         testClassType);

        try {
            result = JMLTranslator.translate(new PositionedString("this.getOne()"),
                                             testClassType, selfVar, null,
                                             null, null, null, Term.class,
                                             services);
        } catch (SLTranslationException e) {
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(termContains(result, selfVar));
        assertTrue(termContains(result, getOne));
    }


    public void testForAll() {
        Term result = null;

        try {
            result = JMLTranslator.translate(
                    new PositionedString(
                    "(\\forall int i; (0 <= i && i <= 2147483647) )"),
                    testClassType, null, null, null, null,
                    null, Term.class, services);
        } catch (SLTranslationException e) {
            assertTrue(e.getMessage(), false);
        }

        assertTrue(result != null);
        assertTrue(result.op().equals(Quantifier.ALL));
        assertTrue(termContains(result, TB.zTerm(services, "2147483647")));
        assertTrue(termContains(result, Junctor.AND));
        LogicVariable i =
                new LogicVariable(new Name("i"),
                                  (Sort) services.getNamespaces().sorts().lookup(new Name(
                "int")));
        Term expected =
                TB.all(i,
                       TB.imp(TB.inInt(TB.var(i), services),
                              TB.and(TB.leq(TB.zTerm(services, "0"),
                                            TB.var(i),
                                            services),
                                     TB.leq(TB.var(i),
                                            TB.zTerm(services, "2147483647"),
                                            services))));
        assertTrue("Result was: " + result + "; \nExpected was: " + expected,
                   result.equalsModRenaming(expected));
    }


    public void testForEx() {
        Term result = null;

        try {
            result = JMLTranslator.translate(
                    new PositionedString(
                    "(\\exists int i; (0 <= i && i <= 2147483647) )"),
                    testClassType, null, null, null, null,
                    null, Term.class, services);
        } catch (SLTranslationException e) {
            assertTrue(e.getMessage(), false);
        }

        assertTrue(result != null);
        assertTrue(result.op().equals(Quantifier.EX));
        assertTrue(termContains(result, TB.zTerm(services, "2147483647")));
        assertTrue(termContains(result, Junctor.AND));
        LogicVariable i =
                new LogicVariable(new Name("i"),
                                  (Sort) services.getNamespaces().sorts().lookup(new Name(
                "int")));
        Term expected =
                TB.ex(i,
                      TB.and(TB.inInt(TB.var(i), services),
                             TB.and(TB.leq(TB.zTerm(services, "0"),
                                           TB.var(i),
                                           services),
                                    TB.leq(TB.var(i),
                                           TB.zTerm(services, "2147483647"),
                                           services))));
        assertTrue("Result was: " + result + "; \nExpected was: " + expected,
                   result.equalsModRenaming(expected));
    }


    public void testBsum() {
        Term result = null;

        try {
            result = JMLTranslator.translate(
                    new PositionedString(
                    "(\\bsum int i; 0; 2147483647; i)"),
                    testClassType, null, null, null, null,
                    null, Term.class, services);
        } catch (SLTranslationException e) {
            assertTrue(e.getMessage(), false);
        }

        NamespaceSet nss = services.getNamespaces();
        Function q = (Function) nss.functions().lookup(new Name("bsum"));
        LogicVariable i =
                new LogicVariable(new Name("i"),
                                  (Sort) nss.sorts().lookup(new Name("int")));
        Term expected =
                TB.bsum(i,
                        TB.zTerm(services, "0"),
                        TB.zTerm(services, "2147483647"),
                        TB.var(i), services);
        assertTrue(result != null);
        assertTrue(result.op().equals(q));
        assertTrue("Result was: " + result + "; \nExpected was: " + expected,
                   result.equalsModRenaming(expected));
    }


    public void testComplexExists() {
        Term result = null;

        try {
            result = JMLTranslator.translate(
                    new PositionedString(
                    "(\\exists TestClass t; t != null; t.i == 0)"),
                    testClassType, null, null, null, null,
                    null, Term.class, services);
        } catch (SLTranslationException e) {
            assertTrue("Error Message: " + e, false);
        }

        assertTrue(result != null);
        assertTrue(result.op().equals(Quantifier.EX));
        assertTrue(result.sub(0).op().equals(Junctor.AND));
        assertTrue(termContains(result, TB.NULL(services)));
    }


    public void testOld() {
        Term result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();
        ProgramVariable excVar = buildExcVar();
        ProgramVariable i = javaInfo.getAttribute("testPackage.TestClass::i");


        try {
            result = JMLTranslator.translate(new PositionedString(
                    "this.i == \\old(this.i)"),
                                                    testClassType, selfVar, null,
                                                    null, excVar, atPres, 
                                                    Term.class, services);
        } catch (SLTranslationException e) {
            e.printStackTrace();
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.op().equals(Equality.EQUALS));
        assertTrue(
                termContains(result,
                             services.getTypeConverter().getHeapLDT().getHeap()));
        assertTrue(termContains(result, atPres.get(services.getTypeConverter().getHeapLDT().getHeap()).op()));
    }


    public void testResultVar() {
        Term result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();
        ProgramVariable excVar = buildExcVar();

        ImmutableList<KeYJavaType> signature =
                ImmutableSLList.<KeYJavaType>nil();

        IProgramMethod pm = javaInfo.getProgramMethod(testClassType, "getOne",
                                                     signature, testClassType);

        ProgramVariable resultVar = buildResultVar(pm);

        try {
            result = JMLTranslator.translate(new PositionedString(
                    "\\result == 1"),
                                                    testClassType, selfVar, null,
                                                    resultVar, excVar, atPres, 
                                                    Term.class, services);
        } catch (SLTranslationException e) {
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.op().equals(Equality.EQUALS));
        assertTrue(termContains(result, resultVar));

    }


    public void testNonNullElements() {
        Term result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();
        ProgramVariable array = javaInfo.getAttribute(
                "testPackage.TestClass::array");

        try {
            result = JMLTranslator.translate(new PositionedString(
                    "\\nonnullelements(this.array)"),
                                                    testClassType,
                                                    selfVar,
                                                    null,
                                                    null,
                                                    null,
                                                    atPres, Term.class,
                                                    services);
        } catch (SLTranslationException e) {
            assertTrue(false);
        }

        assertTrue(result != null);
        //assertTrue(termContains(result.getFormula(), AttributeOp.getAttributeOp(array)));
        assertTrue(termContains(result, TB.NULL(services)));
    }


    public void testIsInitialized() {

        Term result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();

        try {
            result = JMLTranslator.translate(new PositionedString(
                    "\\is_initialized(testPackage.TestClass)"),
                                                    testClassType,
                                                    selfVar,
                                                    null,
                                                    null,
                                                    null,
                                                    atPres, Term.class,
                                                    services);
        } catch (SLTranslationException e) {
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.op().equals(Equality.EQUALS));
        assertTrue(termContains(result, TB.var(
                javaInfo.getAttribute(
                ImplicitFieldAdder.IMPLICIT_CLASS_INITIALIZED,
                                      testClassType))));
    }


    public void testHexLiteral() {
        Term result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();

        try {
            result = JMLTranslator.translate(
                    new PositionedString(" i == 0x12 "),
                    testClassType, selfVar, null, null, null, null, Term.class, services);
        } catch (SLTranslationException e) {
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.op().equals(Equality.EQUALS));
        assertTrue(termContains(result, TB.zTerm(services, "18")));
    }


    public void testComplexQueryResolving1() {
        Term result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();

        ImmutableList<KeYJavaType> signature =
                ImmutableSLList.<KeYJavaType>nil();
        signature = signature.append(javaInfo.getKeYJavaType(
                PrimitiveType.JAVA_INT));

        IProgramMethod pm = javaInfo.getProgramMethod(testClassType, "m",
                                                     signature, testClassType);

        try {
            result = JMLTranslator.translate(
                    new PositionedString("this.m((int)4 + 2) == this.m(i)"),
                    testClassType,
                    selfVar, null, null, null, null, Term.class, services);
        } catch (SLTranslationException e) {
            e.printStackTrace();
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.sub(0).op().equals(pm));
        assertTrue(result.sub(1).op().equals(pm));
    }


    public void testComplexQueryResolving2() {
        Term result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();

        ImmutableList<KeYJavaType> signature =
                ImmutableSLList.<KeYJavaType>nil();
        signature = signature.append(javaInfo.getKeYJavaType(
                PrimitiveType.JAVA_LONG));

        IProgramMethod pm = javaInfo.getProgramMethod(testClassType, "m",
                                                     signature, testClassType);

        try {
            result = JMLTranslator.translate(
                    new PositionedString("this.m(l) == this.m((long)i + 3)"),
                    testClassType, selfVar,
                    null, null, null, null, Term.class, services);
        } catch (SLTranslationException e) {
            e.printStackTrace();
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.sub(0).op().equals(pm));
        assertTrue(result.sub(1).op().equals(pm));
    }


    public void testComplexQueryResolving3() {
        Term result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();

        ImmutableList<KeYJavaType> signature =
                ImmutableSLList.<KeYJavaType>nil();
        signature = signature.append(javaInfo.getKeYJavaType(
                PrimitiveType.JAVA_INT));

        IProgramMethod pm = javaInfo.getProgramMethod(testClassType, "m",
                                                     signature, testClassType);

        try {
            result = JMLTranslator.translate(
                    new PositionedString("this.m(s + 4) == this.m(+b)"),
                    testClassType, selfVar,
                    null, null, null, null, Term.class, services);
        } catch (SLTranslationException e) {
            e.printStackTrace();
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.sub(0).op().equals(pm));
        assertTrue(result.sub(1).op().equals(pm));
    }


    public void testStaticQueryResolving() {
        Term result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();

        ImmutableList<KeYJavaType> signature =
                ImmutableSLList.<KeYJavaType>nil();

        IProgramMethod pm = javaInfo.getProgramMethod(testClassType,
                                                     "staticMethod", signature,
                                                     testClassType);

        try {
            result = JMLTranslator.translate(
                    new PositionedString(
                    "testPackage.TestClass.staticMethod() == 4"), testClassType,
                    selfVar,
                    null, null, null, null, Term.class, services);
        } catch (SLTranslationException e) {
            e.printStackTrace();
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.sub(0).op().equals(pm));
    }


    public void testSubtypeExpression() {
        Term result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();

        try {
            result = JMLTranslator.translate(
                    new PositionedString(
                    "( \\exists TestClass t; t != null; \\typeof(t) <: \\type(java.lang.Object) )"),
                    testClassType, selfVar,
                    null, null, null, null, Term.class, services);
        } catch (SLTranslationException e) {
            e.printStackTrace();
            assertTrue(false);
        }

        assertTrue(result != null);

        Sort sds = javaInfo.objectSort();
        Function ioFunc = sds.getInstanceofSymbol(services);
        assertTrue(termContains(result, ioFunc));
    }


    public void testCorrectImplicitThisResolution() {
        Term result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();
        LocationVariable array = (LocationVariable) javaInfo.getAttribute(
                "testPackage.TestClass::array");

        try {
            result = JMLTranslator.translate(new PositionedString(
                    "(\\forall TestClass a;a.array == array; a == this)"),
                                                    testClassType,
                                                    selfVar,
                                                    null,
                                                    null,
                                                    null,
                                                    null,
                                                    Term.class,
                                                    services);
        } catch (SLTranslationException e) {
            assertTrue("Parsing Error: " + e, false);
        }

        assertTrue(result != null);
        final LogicVariable qv =
                new LogicVariable(new Name("a"), selfVar.sort());
        final Function fieldSymbol = services.getTypeConverter().getHeapLDT().getFieldSymbolForPV(
                array, services);
        Term expected = TB.all(qv,
                               TB.imp(
                TB.and(TB.and(TB.equals(TB.dot(services,
                                               array.sort(),
                                               TB.var(qv),
                                               fieldSymbol),
                                        TB.dot(services,
                                               array.sort(),
                                               TB.var(selfVar),
                                               fieldSymbol)),
                              TB.reachableValue(services,
                                                TB.var(qv),
                                                selfVar.getKeYJavaType())),
                       TB.not(TB.equals(TB.var(qv),
                                        TB.NULL(services)))), // implicit non null
                                      TB.equals(TB.var(qv), TB.var(selfVar))));
        assertTrue("Expected:" + ProofSaver.printTerm(expected, services)
                   + "\n Was:" + ProofSaver.printTerm(result, services),
                   result.equalsModRenaming(expected));
    }
}
