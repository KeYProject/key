// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.


package de.uka.ilkd.key.speclang.ocl.translation;

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
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.init.CreatedAttributeTermFactory;
import de.uka.ilkd.key.speclang.FormulaWithAxioms;
import de.uka.ilkd.key.speclang.ocl.translation.OCLTranslator;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.util.HelperClassForTests;
import junit.framework.TestCase;

public class TestOCLTranslator extends TestCase {

    public static final String testFile = System.getProperty("key.home")
            + File.separator + "examples" + File.separator + "_testcase"
            + File.separator + "speclang" + File.separator + "testFile.key";

    private static final TermBuilder tb = TermBuilder.DF;
    
    private static JavaInfo javaInfo;
    private static Services services;
    private static OCLTranslator translator;
    private static KeYJavaType testClassType;
    
    
    protected void setUp() {
        if(javaInfo != null) {
            return;
        }
        javaInfo = new HelperClassForTests().parse(new File(testFile)).getFirstProof().getJavaInfo();
        services = javaInfo.getServices();
        translator = new OCLTranslator(services);
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
                .getTypeByClassName("java.lang.Throwable");
        ProgramElementName excPEN = new ProgramElementName("exc");
        return new LocationVariable(excPEN, excType);
    }

    public void testTrueTerm() {
        FormulaWithAxioms result = null;

        try {
            result = translator.translateExpression("true", javaInfo
                    .getKeYJavaType("testPackage.TestClass"), null, null, null,
                    null, new LinkedHashMap());
        } catch (SLTranslationException e) {
            assertTrue(false);
        }
        assertTrue(result != null);

        assert result != null;
        assertTrue(result.getFormula().equals(TermBuilder.DF.tt()));
        assertTrue(result.getAxioms().isEmpty());
    }

    public void testSelfVar() {
        FormulaWithAxioms result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();

        try {
            result = translator.translateExpression("self", testClassType,
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
            result = translator.translateExpression("self.i", testClassType,
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
            result = translator.translateExpression("self.getOne()",
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
                    "TestClass.allInstances()->forAll(t | t <> null)",
                    this.testClassType, null, null, null, null,
                    new LinkedHashMap());
        } catch (SLTranslationException e) {
            e.printStackTrace();
            assertTrue(false);
        }

        assertTrue(result != null);

        assert result != null;
        /*
         System.out.println("nr. of axioms: " + result.getAxioms().size());
         Iterator it = result.getAxioms().keySet().iterator();
         while(it.hasNext()) {
         Operator op = (Operator) it.next();
         System.out.println("axiom for " + op + ": " + result.getAxioms().get(op));
         }
         System.out.println();
         System.out.println("formula: " + result.getFormula());
         System.out.println();
         System.out.println();
         */
        // There sould be 1 axiom defining allInstances (in functional representation)
        assertTrue(result.getAxioms().size() == 1);
        assertTrue(result.getFormula().op().equals(Op.ALL));
        assertTrue(result.getFormula().sub(0).op().equals(Op.IMP));
        assertTrue(result.getFormula().varsBoundHere(0).size() == 1);
        LogicVariable q = (LogicVariable) result.getFormula().varsBoundHere(0)
                .getQuantifiableVariable(0);

        Term subTerm = tb.imp(CreatedAttributeTermFactory.INSTANCE
                .createCreatedOrNullTerm(services, tb.var(q)), tb.imp(tb.not(tb
                .equals(tb.var(q), tb.NULL(services))), tb.not(tb.equals(tb
                .var(q), tb.NULL(services)))));
        Term expectedTerm = tb.all(q, subTerm);
        assertTrue(result.getFormula().equals(expectedTerm));
    }

    public void testComplexExists() {
        FormulaWithAxioms result = null;

        try {
            result = translator
                    .translateExpression(
                            "TestClass.allInstances()->select(t | t <> null)->exists(t | t = null)",
                            this.testClassType, null, null, null, null,
                            new LinkedHashMap());
        } catch (SLTranslationException e) {
            e.printStackTrace();
            assertTrue(false);
        }

        assertTrue(result != null);

        assert result != null;
        /*
         System.out.println("nr. of axioms: " + result.getAxioms().size());
         Iterator it = result.getAxioms().keySet().iterator();
         while(it.hasNext()) {
         Operator op = (Operator) it.next();
         System.out.println("axiom for " + op + ": " + result.getAxioms().get(op));
         }
         System.out.println();
         System.out.println("formula: " + result.getFormula());
         System.out.println();
         System.out.println();
         */
        // There sould be 1 axiom defining allInstances (in functional representation)
        // and 1 axiom defining the call to select
        assertTrue(result.getAxioms().size() == 2);
        assertTrue(result.getFormula().op().equals(Op.EX));
        assertTrue(result.getFormula().sub(0).op().equals(Op.AND));
        assertTrue(result.getFormula().varsBoundHere(0).size() == 1);
    }

    public void testAtPre() {
        FormulaWithAxioms result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();
        ProgramVariable excVar = buildExcVar();

        Map<Operator, Function> atPreDefs = new LinkedHashMap<Operator, Function>();

        try {
            result = translator.translateExpression("self.i = self.i@pre",
                    testClassType, selfVar, null, null, excVar, // needed to make the translator think it's a postcondition
                    atPreDefs);
        } catch (SLTranslationException e) {
            e.printStackTrace();
            assertTrue(false);
        }

        assertTrue(result != null);

        assert result != null;
        assertTrue(result.getAxioms().isEmpty());
        assertTrue(atPreDefs.size() == 1);
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
                    "self.m(4 + 2) = self.m(i)", testClassType, selfVar,
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
                    "self.m(l) = self.m(i.oclAsType(long))", testClassType,
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

}
