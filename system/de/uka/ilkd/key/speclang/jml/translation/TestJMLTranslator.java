// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.




package de.uka.ilkd.key.speclang.jml.translation;

import java.io.File;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.ListOfKeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.SLListOfKeYJavaType;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.FormulaWithAxioms;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.util.HelperClassForTests;

import junit.framework.TestCase;


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
    
    

    protected void setUp() {
        if(javaInfo != null) {
            return;
        }
        javaInfo = new HelperClassForTests().parse(
                new File(testFile)).getFirstProof().getJavaInfo();
        services = javaInfo.getServices();
        translator = new JMLTranslator(services);
        testClassType = javaInfo.getKeYJavaType("testPackage.TestClass");
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
                .getTypeByClassName("java.lang.Exception");
        ProgramElementName excPEN = new ProgramElementName("exc");
        return new LocationVariable(excPEN, excType);
    }

    
    public void testTrueTerm() {
        FormulaWithAxioms result = null;

        try {
            result = translator.translateExpression(new PositionedString("true"), testClassType,
                    null, null, null, null, new LinkedHashMap());
        } catch (SLTranslationException e) {
            assertTrue(false);
        }

        assertTrue(result != null);

        assert result != null;
        assertTrue(result.getFormula().equals(tb.tt()));
        assertTrue(result.getAxioms().isEmpty());
    }

    
    public void testSelfVar() {
        FormulaWithAxioms result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();

        try {
            result = translator.translateExpression(new PositionedString("this"), testClassType,
                    selfVar, null, null, null, new LinkedHashMap());
        } catch (SLTranslationException e) {
            assertTrue(false);
        }

        assertTrue(result != null);
        assert result != null;
        assertTrue(result.getFormula().equals(tb.var(selfVar)));
        assertTrue(result.getAxioms().isEmpty());
    }

    
    public void testPrimitiveField() {
        FormulaWithAxioms result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();
        ProgramVariable i = javaInfo.getAttribute("testPackage.TestClass::i");

        try {
            result = translator.translateExpression(new PositionedString("this.i"), testClassType,
                    selfVar, null, null, null, new LinkedHashMap());
        } catch (SLTranslationException e) {
            assertTrue(false);
        }

        assertTrue(result != null);

        assert result != null;
        assertTrue(result.getFormula().equals(tb.dot(tb.var(selfVar), i)));
        assertTrue(result.getAxioms().isEmpty());
    }

    
    public void testSimpleQuery() {
        FormulaWithAxioms result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();
        Term queryTerm = javaInfo.getProgramMethodTerm(tb.var(selfVar),
                "getOne", new Term[] {}, "testPackage.TestClass");

        try {
            result = translator.translateExpression(new PositionedString("this.getOne()"),
                    testClassType, selfVar, null, null, null,
                    new LinkedHashMap());
        } catch (SLTranslationException e) {
            assertTrue(false);
        }

        assertTrue(result != null);

        assert result != null;
        assertTrue(result.getFormula().equals(queryTerm));
        assertTrue(result.getAxioms().isEmpty());
    }

    
    public void testForAll() {
        FormulaWithAxioms result = null;

        try {
            result = translator.translateExpression(
                    new PositionedString("(\\forall int i; (-2147483648 <= i && i <= 2147483647) )"),
                    this.testClassType, null, null, null, null,
                    new LinkedHashMap());
        } catch (SLTranslationException e) {
            assertTrue(false);
        }

        assertTrue(result != null);

        assert result != null;
        assertTrue(result.getAxioms().isEmpty());
        assertTrue(result.getFormula().op().equals(Op.ALL));
        assertTrue(result.getFormula().sub(0).op().equals(Op.AND));
        assertTrue(result.getFormula().sub(0).sub(0).op() instanceof Function);
        assertTrue(((Function) result.getFormula().sub(0).sub(0).op()).name()
                .toString().equals("leq"));
    }

    
    public void testComplexExists() {
        FormulaWithAxioms result = null;

        try {
            result = translator.translateExpression(
                    new PositionedString("(\\exists TestClass t; t != null; t.i == 0) )"),
                    this.testClassType, null, null, null, null,
                    new LinkedHashMap());
        } catch (SLTranslationException e) {
            assertTrue(false);
        }

        assertTrue(result != null);

        assert result != null;
        assertTrue(result.getAxioms().isEmpty());
        assertTrue(result.getFormula().op().equals(Op.EX));
        assertTrue(result.getFormula().sub(0).op().equals(Op.AND));
    }


    public void testOld() {
        FormulaWithAxioms result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();
        ProgramVariable excVar = buildExcVar();

        Map atPreDefs = new LinkedHashMap();

        try {
            result = translator.translateExpression(new PositionedString("this.i == \\old(this.i)"),
                    testClassType, selfVar, null, null, excVar, atPreDefs);
        } catch (SLTranslationException e) {
            e.printStackTrace();
            assertTrue(false);
        }

        assertTrue(result != null);

        assert result != null;
        assertTrue(result.getAxioms().isEmpty());
        assertTrue(atPreDefs.size() == 2); // one for "this" and one for "i"
        assertTrue(result.getFormula().op().equals(Op.EQUALS));
    }

    
    public void testComplexQueryResolving1() {
        FormulaWithAxioms result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();

        ListOfKeYJavaType signature = SLListOfKeYJavaType.EMPTY_LIST;
        signature = signature.append(javaInfo
                .getKeYJavaType(PrimitiveType.JAVA_INT));

        ProgramMethod pm = javaInfo.getProgramMethod(testClassType, "m",
                signature, testClassType);

        try {
            result = translator.translateExpression(
                    new PositionedString("this.m((long) 4 + 2) == this.m(l+i)"), testClassType,
                    selfVar, null, null, null, new LinkedHashMap());
        } catch (SLTranslationException e) {
            e.printStackTrace();
            assertTrue(false);
        }

        assertTrue(result != null);

        assert result != null;
        assertTrue(result.getAxioms().isEmpty());
        assertTrue(result.getFormula().sub(0).op().equals(pm));
        assertTrue(result.getFormula().sub(1).op().equals(pm));
    }

    
    public void testComplexQueryResolving2() {
        FormulaWithAxioms result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();

        ListOfKeYJavaType signature = SLListOfKeYJavaType.EMPTY_LIST;
        signature = signature.append(javaInfo
                .getKeYJavaType(PrimitiveType.JAVA_LONG));

        ProgramMethod pm = javaInfo.getProgramMethod(testClassType, "m",
                signature, testClassType);

        try {
            result = translator.translateExpression(
                    new PositionedString("this.m(l) == this.m((long)i)"), testClassType, selfVar,
                    null, null, null, new LinkedHashMap());
        } catch (SLTranslationException e) {
            e.printStackTrace();
            assertTrue(false);
        }

        assertTrue(result != null);

        assert result != null;
        assertTrue(result.getAxioms().isEmpty());
        assertTrue(result.getFormula().sub(0).op().equals(pm));
        assertTrue(result.getFormula().sub(1).op().equals(pm));
    }


    public void testStaticQueryResolving() {
        FormulaWithAxioms result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();

        ListOfKeYJavaType signature = SLListOfKeYJavaType.EMPTY_LIST;

        ProgramMethod pm = javaInfo.getProgramMethod(testClassType,
                "staticMethod", signature, testClassType);

        try {
            result = translator.translateExpression(
                    new PositionedString("testPackage.TestClass.staticMethod() == 4"), testClassType, selfVar,
                    null, null, null, new LinkedHashMap());
        } catch (SLTranslationException e) {
            e.printStackTrace();
            assertTrue(false);
        }

        assertTrue(result != null);

        assert result != null;
        assertTrue(result.getAxioms().isEmpty());
        assertTrue(result.getFormula().sub(0).op().equals(pm));
    }
}
