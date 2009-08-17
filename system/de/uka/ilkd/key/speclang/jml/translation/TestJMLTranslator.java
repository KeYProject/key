// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.




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
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.ProofSaver;
import de.uka.ilkd.key.speclang.FormulaWithAxioms;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.SignatureVariablesFactory;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.util.HelperClassForTests;


public class TestJMLTranslator extends TestCase {

    public static final String testFile = System.getProperty("key.home")
            + File.separator + "examples"
            + File.separator + "_testcase"
            + File.separator + "speclang"
            + File.separator + "testFile.key";

    private static final TermBuilder tb = TermBuilder.DF;

    private static JavaInfo javaInfo;
    private static Services services;
    private static JMLTranslator translator;
    private static KeYJavaType testClassType;
    
    private static Term heapAtPre;
        

    protected void setUp() {
        if(javaInfo != null) {
            return;
        }
        javaInfo = new HelperClassForTests().parse(
                new File(testFile)).getFirstProof().getJavaInfo();
        services = javaInfo.getServices();
        translator = new JMLTranslator(services);
        testClassType = javaInfo.getKeYJavaType("testPackage.TestClass");
        heapAtPre = tb.func(SignatureVariablesFactory.INSTANCE.createHeapAtPreFunc(services, false));        
    }

    
    protected void tearDown() {
    }

    
    protected ProgramVariable buildSelfVarAsProgVar() {
        ProgramElementName classPEN = new ProgramElementName("self");
        ProgramVariable result = new LocationVariable(classPEN, testClassType);
        return result;
    }

    
    protected ProgramVariable buildExcVar() {
        KeYJavaType excType = javaInfo
                .getTypeByClassName("java.lang.Throwable");
        ProgramElementName excPEN = new ProgramElementName("exc");
        return new LocationVariable(excPEN, excType);
    }

    
    protected ProgramVariable buildResultVar(ProgramMethod pm) {
        ProgramElementName resPEN = new ProgramElementName("result");
        ProgramVariable result = new LocationVariable(resPEN, pm.getKeYJavaType());
        return result;
    }
    
    
    private boolean termContains(Term t, Term sub) {
        
        for(int i = 0; i < t.arity(); i++) {
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
        
        for(int i = 0; i < t.arity(); i++) {
            if (termContains(t.sub(i), op)) {
                return true;
            }
        }
        
        return false;
    }

    
    public void testTrueTerm() {
        FormulaWithAxioms result = null;

        try {
            result = translator.translateExpression(new PositionedString("true"), testClassType,
                    null, null, null, null, null);
        } catch (SLTranslationException e) {
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.getFormula().equals(tb.tt()));
        assertTrue(result.getAxioms().isEmpty());
    }

    
    public void testSelfVar() {
        FormulaWithAxioms result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();

        try {
            result = translator.translateExpression(new PositionedString("this"), testClassType,
                    selfVar, null, null, null, null);
        } catch (SLTranslationException e) {
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.getFormula().equals(tb.var(selfVar)));
        assertTrue(result.getAxioms().isEmpty());
    }

    
    public void testLogicalExpression() {
        FormulaWithAxioms result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();

        try {
            result = translator.translateExpression(new PositionedString("(b <= s &&  i > 5) ==> this != instance"), testClassType,
                    selfVar, null, null, null, null);
        } catch (SLTranslationException e) {
            e.printStackTrace();
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.getAxioms().isEmpty());
        assertTrue(result.getFormula().op().equals(Junctor.IMP));
        assertTrue(result.getFormula().sub(0).op().equals(Junctor.AND));
        assertTrue(termContains(result.getFormula(), tb.zTerm(services, "5")));
        assertTrue(termContains(result.getFormula(), selfVar));
    }
    
    
    public void testPrimitiveField() {
        FormulaWithAxioms result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();
        ProgramVariable i = javaInfo.getAttribute("testPackage.TestClass::i");

        try {
            result = translator.translateExpression(new PositionedString("this.i"), testClassType,
                    selfVar, null, null, null, null);
        } catch (SLTranslationException e) {
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.getAxioms().isEmpty());
        //assertTrue(termContains(result.getFormula(), AttributeOp.getAttributeOp(i) ));
        assertTrue(termContains(result.getFormula(), selfVar ));
    }

    
    public void testSimpleQuery() {
        FormulaWithAxioms result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();
        ProgramMethod getOne = javaInfo.getProgramMethod(testClassType,
                "getOne", ImmutableSLList.<KeYJavaType>nil(), testClassType);

        try {
            result = translator.translateExpression(new PositionedString("this.getOne()"),
                    testClassType, selfVar, null, null, null,
                    null);
        } catch (SLTranslationException e) {
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.getAxioms().isEmpty());
        assertTrue(termContains(result.getFormula(), selfVar));
        assertTrue(termContains(result.getFormula(), getOne));
    }

    
    public void testForAll() {
        FormulaWithAxioms result = null;

        try {
            result = translator.translateExpression(
                    new PositionedString("(\\forall int i; (-2147483648 <= i && i <= 2147483647) )"),
                    testClassType, null, null, null, null,
                    null);
        } catch (SLTranslationException e) {
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.getAxioms().isEmpty());
        assertTrue(result.getFormula().op().equals(Quantifier.ALL));
        assertTrue(termContains(result.getFormula(), tb.zTerm(services, "2147483647")));
        assertTrue(termContains(result.getFormula(), Junctor.AND));
    }

    
    public void testComplexExists() {
        FormulaWithAxioms result = null;

        try {
            result = translator.translateExpression(
                    new PositionedString("(\\exists TestClass t; t != null; t.i == 0) )"),
                    testClassType, null, null, null, null,
                    null);
        } catch (SLTranslationException e) {
            assertTrue("Error Message: "+e,false);
        }

        assertTrue(result != null);
        assertTrue(result.getAxioms().isEmpty());
        assertTrue(result.getFormula().op().equals(Quantifier.EX));
        assertTrue(result.getFormula().sub(0).op().equals(Junctor.AND));
        assertTrue(termContains(result.getFormula(), tb.NULL(services)));
    }


    public void testOld() {
        FormulaWithAxioms result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();
        ProgramVariable excVar = buildExcVar();
        ProgramVariable i = javaInfo.getAttribute("testPackage.TestClass::i");


        try {
            result = translator.translateExpression(new PositionedString("this.i == \\old(this.i)"),
                    testClassType, selfVar, null, null, excVar, heapAtPre);
        } catch (SLTranslationException e) {
            e.printStackTrace();
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.getAxioms().isEmpty());
        assertTrue(result.getFormula().op().equals(Equality.EQUALS));
        assertTrue(termContains(result.getFormula(), services.getTypeConverter().getHeapLDT().getHeap()));        
        assertTrue(termContains(result.getFormula(), heapAtPre.op()));
    }

    
    public void testResultVar() {
        FormulaWithAxioms result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();
        ProgramVariable excVar = buildExcVar();
        
        ImmutableList<KeYJavaType> signature = ImmutableSLList.<KeYJavaType>nil();

        ProgramMethod pm = javaInfo.getProgramMethod(testClassType, "getOne",
                signature, testClassType);
        
        ProgramVariable resultVar = buildResultVar(pm);

        try {
            result = translator.translateExpression(new PositionedString("\\result == 1"),
                    testClassType, selfVar, null, resultVar, excVar, heapAtPre);
        } catch (SLTranslationException e) {
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.getAxioms().isEmpty());
        assertTrue(result.getFormula().op().equals(Equality.EQUALS));
        assertTrue(termContains(result.getFormula(), resultVar));
        
    }

    
    public void testCreated() {
        FormulaWithAxioms result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();
        Function instance = services.getTypeConverter()
                                    .getHeapLDT()
                                    .getFieldSymbolForPV((LocationVariable)javaInfo.getAttribute("testPackage.TestClass::instance"), 
                                	                 services);

        try {
            result = translator.translateExpression(new PositionedString("\\created(this.instance)"),
                    testClassType, selfVar, null, null, null, heapAtPre);
        } catch (SLTranslationException e) {
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.getAxioms().isEmpty());
        assertTrue(termContains(result.getFormula(), instance));
        //assertTrue(termContains(result.getFormula(), AttributeOp
        //        .getAttributeOp(javaInfo.getAttribute(
        //                ImplicitFieldAdder.IMPLICIT_CREATED, javaInfo
        //                        .getJavaLangObject()))));
    }

    
    public void testNonNullElements() {
        FormulaWithAxioms result = null;
        
        ProgramVariable selfVar = buildSelfVarAsProgVar();
        ProgramVariable array = javaInfo.getAttribute("testPackage.TestClass::array");
        
        try {
            result = translator.translateExpression(new PositionedString("\\nonnullelements(this.array)"),
                    testClassType,
                    selfVar,
                    null,
                    null,
                    null,
                    heapAtPre);
        } catch (SLTranslationException e) {
            assertTrue(false);
        }
        
        assertTrue(result != null);
        assertTrue(result.getAxioms().isEmpty());
        //assertTrue(termContains(result.getFormula(), AttributeOp.getAttributeOp(array)));
        assertTrue(termContains(result.getFormula(), tb.NULL(services)));
    }

    
    public void testIsInitialized() {
        
        FormulaWithAxioms result = null;
        
        ProgramVariable selfVar = buildSelfVarAsProgVar();
        
        try {
            result = translator.translateExpression(new PositionedString("\\is_initialized(testPackage.TestClass)"),
                    testClassType,
                    selfVar,
                    null,
                    null,
                    null,
                    heapAtPre);
        } catch (SLTranslationException e) {
            assertTrue(false);
        }
        
        assertTrue(result != null);
        assertTrue(result.getAxioms().isEmpty());
        assertTrue(result.getFormula().op().equals(Equality.EQUALS));
        assertTrue(termContains(result.getFormula(), tb.var(javaInfo
                .getAttribute(ImplicitFieldAdder.IMPLICIT_CLASS_INITIALIZED,
                        testClassType))));
    }

  
    public void testHexLiteral() {
        FormulaWithAxioms result = null;
        
        ProgramVariable selfVar = buildSelfVarAsProgVar();
        
        try {
            result = translator.translateExpression(
                    new PositionedString(" i == 0x12 "),
                    testClassType, selfVar, null, null, null, null);
        } catch (SLTranslationException e) {
            assertTrue(false);
        }
        
        assertTrue(result != null);
        assertTrue(result.getFormula().op().equals(Equality.EQUALS));
        assertTrue(termContains(result.getFormula(),tb.zTerm(services, "18")));
    }
    
    
    public void testComplexQueryResolving1() {
        FormulaWithAxioms result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();

        ImmutableList<KeYJavaType> signature = ImmutableSLList.<KeYJavaType>nil();
        signature = signature.append(javaInfo
                .getKeYJavaType(PrimitiveType.JAVA_INT));

        ProgramMethod pm = javaInfo.getProgramMethod(testClassType, "m",
                signature, testClassType);

        try {
            result = translator.translateExpression(
                    new PositionedString("this.m((int)4 + 2) == this.m(i)"), testClassType,
                    selfVar, null, null, null, null);
        } catch (SLTranslationException e) {
            e.printStackTrace();
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.getAxioms().isEmpty());
        assertTrue(result.getFormula().sub(0).op().equals(pm));
        assertTrue(result.getFormula().sub(1).op().equals(pm));
    }

    
    public void testComplexQueryResolving2() {
        FormulaWithAxioms result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();

        ImmutableList<KeYJavaType> signature = ImmutableSLList.<KeYJavaType>nil();
        signature = signature.append(javaInfo
                .getKeYJavaType(PrimitiveType.JAVA_LONG));

        ProgramMethod pm = javaInfo.getProgramMethod(testClassType, "m",
                signature, testClassType);

        try {
            result = translator.translateExpression(
                    new PositionedString("this.m(l) == this.m((long)i + 3)"), testClassType, selfVar,
                    null, null, null, null);
        } catch (SLTranslationException e) {
            e.printStackTrace();
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.getAxioms().isEmpty());
        assertTrue(result.getFormula().sub(0).op().equals(pm));
        assertTrue(result.getFormula().sub(1).op().equals(pm));
    }


    public void testComplexQueryResolving3() {
        FormulaWithAxioms result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();

        ImmutableList<KeYJavaType> signature = ImmutableSLList.<KeYJavaType>nil();
        signature = signature.append(javaInfo
                .getKeYJavaType(PrimitiveType.JAVA_INT));

        ProgramMethod pm = javaInfo.getProgramMethod(testClassType, "m",
                signature, testClassType);

        try {
            result = translator.translateExpression(
                    new PositionedString("this.m(s + 4) == this.m(+b)"), testClassType, selfVar,
                    null, null, null, null);
        } catch (SLTranslationException e) {
            e.printStackTrace();
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.getAxioms().isEmpty());
        assertTrue(result.getFormula().sub(0).op().equals(pm));
        assertTrue(result.getFormula().sub(1).op().equals(pm));
    }


    public void testStaticQueryResolving() {
        FormulaWithAxioms result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();

        ImmutableList<KeYJavaType> signature = ImmutableSLList.<KeYJavaType>nil();

        ProgramMethod pm = javaInfo.getProgramMethod(testClassType,
                "staticMethod", signature, testClassType);

        try {
            result = translator.translateExpression(
                    new PositionedString("testPackage.TestClass.staticMethod() == 4"), testClassType, selfVar,
                    null, null, null, null);
        } catch (SLTranslationException e) {
            e.printStackTrace();
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.getAxioms().isEmpty());
        assertTrue(result.getFormula().sub(0).op().equals(pm));
    }
    
    
    public void testSubtypeExpression() {
        FormulaWithAxioms result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();

        try {
            result = translator.translateExpression(
                    new PositionedString("( \\exists TestClass t; t != null; \\typeof(t) <: \\type(java.lang.Object) )"), testClassType, selfVar,
                    null, null, null, null);
        } catch (SLTranslationException e) {
            e.printStackTrace();
            assertTrue(false);
        }

        assertTrue(result != null);

        Sort sds = javaInfo.objectSort();
        Function ioFunc = sds.getInstanceofSymbol(services);
        assertTrue(termContains(result.getFormula(), ioFunc));
    }
    
    
    public void testCorrectImplicitThisResolution() {
        FormulaWithAxioms result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();
        LocationVariable array 
        	= (LocationVariable) javaInfo.getAttribute("testPackage.TestClass::array");

        try {
            result = translator.translateExpression
                (new PositionedString("(\\forall TestClass a;a.array == array; a == this)"),
                    testClassType,
                    selfVar,
                    null,
                    null,
                    null,
                    null);
        } catch (SLTranslationException e) {
            assertTrue("Parsing Error: "+e,false);
        }

        assertTrue(result != null);
        final LogicVariable qv = new LogicVariable(new Name("a"),selfVar.sort());
        final Function fieldSymbol = services.getTypeConverter().getHeapLDT().getFieldSymbolForPV(array, services);
        Term expected = tb.all(qv,
                tb.imp(tb.and(
                        tb.equals(tb.dot(services, array.sort(), tb.var(qv), fieldSymbol),
                        	  tb.dot(services, array.sort(), tb.var(selfVar), fieldSymbol)),
                        tb.not(tb.equals(tb.var(qv), tb.NULL(services))) // implicit non null
                        ),
                        tb.equals(tb.var(qv), tb.var(selfVar))));
        assertTrue("Expected:"+ProofSaver.printTerm(expected,services)+"\n Was:"+
                ProofSaver.printTerm(result.getFormula(),services),
                result.getFormula().equalsModRenaming(expected));
    } 
}
