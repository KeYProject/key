package de.uka.ilkd.key.suite;
// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

import junit.framework.TestCase;
import junit.framework.TestResult;
import junit.framework.TestSuite;

@SuppressWarnings("unchecked")
public class TestKey extends TestSuite {

    static Class<? extends TestCase>[] utilityTests = new Class[] {
        de.uka.ilkd.key.util.TestLexicographicComparator.class,
        de.uka.ilkd.key.util.TestVersionStringComparator.class,
        de.uka.ilkd.key.util.TestMiscTools.class,
        de.uka.ilkd.key.util.pp.TestLayouter.class,
        de.uka.ilkd.key.util.TestProofStarter.class,
        de.uka.ilkd.key.util.TestNodePreorderIterator.class,
        de.uka.ilkd.key.util.TestProofUserManager.class,
        de.uka.ilkd.key.rule.join.PredicateAbstractionLatticeTests.class
    }; 


    static Class<? extends TestCase>[] logicModelTests = new Class[] {
        de.uka.ilkd.key.logic.TestTermFactory.class,
        de.uka.ilkd.key.logic.TestTermLabelManager.class,
        de.uka.ilkd.key.logic.TestTermBuilder.class,
        de.uka.ilkd.key.logic.TestTerm.class,
        de.uka.ilkd.key.logic.TestNamespace.class,
        de.uka.ilkd.key.logic.TestSemisequent.class,
        de.uka.ilkd.key.logic.TestPosInOcc.class,   	
        de.uka.ilkd.key.logic.TestPosInTerm.class,       
        de.uka.ilkd.key.logic.TestClashFreeSubst.class,
        de.uka.ilkd.key.logic.TestSyntacticalReplaceVisitor.class,
        de.uka.ilkd.key.logic.TestVariableNamer.class,
        de.uka.ilkd.key.logic.LabeledTermImplTest.class
    };


    static Class<? extends TestCase>[] parserTests = new Class[] {
        de.uka.ilkd.key.parser.TestDeclParser.class,
//        de.uka.ilkd.key.parser.TestParallelParsing.class,
        de.uka.ilkd.key.parser.TestTermParser.class,
        de.uka.ilkd.key.parser.TestTermParserHeap.class,
        de.uka.ilkd.key.parser.TestTermParserSorts.class,
        de.uka.ilkd.key.parser.TestJMLParserAssociativity.class,
        de.uka.ilkd.key.parser.TestTacletParser.class,
    };


    static Class<? extends TestCase>[] ruleTests = new Class[] {
        de.uka.ilkd.key.rule.TestSchemaModalOperators.class,
        de.uka.ilkd.key.rule.tacletbuilder.TestTacletBuild.class,
        de.uka.ilkd.key.rule.TestCollisionResolving.class,
        de.uka.ilkd.key.rule.TestMatchTaclet.class,
        de.uka.ilkd.key.rule.match.legacy.TestLegacyTacletMatch.class,
        de.uka.ilkd.key.rule.match.vm.VMTacletMatcherTest.class,
        de.uka.ilkd.key.rule.TestApplyTaclet.class,
        de.uka.ilkd.key.rule.inst.TestGenericSortInstantiations.class,
        de.uka.ilkd.key.rule.metaconstruct.TestProgramMetaConstructs.class,
        de.uka.ilkd.key.rule.conditions.TestDropEffectlessElementary.class,
        de.uka.ilkd.key.rule.join.JoinRuleTests.class
    };


    static Class<? extends TestCase>[] proofConstructionTests = new Class[] {
        de.uka.ilkd.key.proof.TestTacletIndex.class,
        de.uka.ilkd.key.proof.TestProofTree.class,
        de.uka.ilkd.key.proof.TestGoal.class,
        de.uka.ilkd.key.proof.TestTermTacletAppIndex.class,
        de.uka.ilkd.key.taclettranslation.TestTacletTranslator.class,
        de.uka.ilkd.key.taclettranslation.lemma.TestGenericRemovingLemmaGenerator.class
    };


    static Class<? extends TestCase>[] javaTests = new Class[] {
        de.uka.ilkd.key.java.TestJavaInfo.class,
        de.uka.ilkd.key.java.TestJavaCardDLJavaExtensions.class,
        de.uka.ilkd.key.java.TestRecoder2KeY.class,
        de.uka.ilkd.key.java.TestKeYRecoderMapping.class,
        de.uka.ilkd.key.java.visitor.TestDeclarationProgramVariableCollector.class,
        de.uka.ilkd.key.java.TestContextStatementBlock.class
    };


    static Class<? extends TestCase>[] speclangTests = new Class[] {
        de.uka.ilkd.key.speclang.jml.translation.TestJMLTranslator.class,
        de.uka.ilkd.key.speclang.jml.pretranslation.TestJMLPreTranslator.class
    };


    static Class<? extends TestCase>[] smtTests = new Class[] {
        de.uka.ilkd.key.smt.test.TestSimplify.class,
        de.uka.ilkd.key.smt.test.TestZ3.class,
        de.uka.ilkd.key.smt.test.TestYices.class,
        de.uka.ilkd.key.smt.test.TestCvc3.class
        //, de.uka.ilkd.key.smt.test.TestCvc4.class  //commented out as test take too long
    };


    public static TestSuite createSuite(Class<? extends TestCase>[] testClasses, final String msg) {
        TestSuite suite = new TestSuite() {
            @Override
            public void run(TestResult result) {
                System.out.print("[" + msg + "]: ");
                super.run(result);
                System.out.println();
            }
        };

        for ( int i = 0; i < testClasses.length; i++ ) {
            suite.addTest(new TestSuite(testClasses[i]));
        }

        return suite;
    }


    public static junit.framework.Test suite() {
	de.uka.ilkd.key.util.Debug.ENABLE_DEBUG = false;

        TestSuite suite = new TestSuite();
        suite.addTest(createSuite(utilityTests, "Testing KeY specific Utilities"));
        suite.addTest(createSuite(logicModelTests, "Testing Logic Engine"));	
        suite.addTest(createSuite(parserTests, "Testing Parsers"));
        suite.addTest(createSuite(ruleTests, "Testing Rule Engine"));
        suite.addTest(createSuite(proofConstructionTests, "Testing Proof Construction"));
        suite.addTest(createSuite(javaTests, "Testing Java Datastructures"));
        suite.addTest(createSuite(speclangTests, "Testing JML frontend"));
        suite.addTest(createSuite(smtTests, "Testing SMT backend"));
        suite.addTest(createSuite(new Class[]{de.uka.ilkd.key.util.DesignTests.class}, "Test Design Constraints"));

        return suite;
    }
    

    public TestKey(String name) {
        super(name);
    }
}