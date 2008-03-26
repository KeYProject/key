// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

import junit.framework.TestCase;
import junit.framework.TestSuite;
import junit.framework.TestResult;

public class TestKey extends TestCase {

     static Class[] utilityTests = new Class[] {
   	de.uka.ilkd.key.collection.TestSetAsListOfString.class,
   	de.uka.ilkd.key.collection.TestSLListOfString.class,
   	de.uka.ilkd.key.collection.TestMapAsListFromIntegerToString.class,
 	de.uka.ilkd.key.collection.TestLeftistHeapOfInteger.class,
	de.uka.ilkd.key.util.pp.TestLayouter.class
     }; 

     static Class[] parserTests = new Class[] {
   	de.uka.ilkd.key.parser.TestDeclParser.class,
   	de.uka.ilkd.key.parser.TestTermParser.class,
  	de.uka.ilkd.key.parser.TestTacletParser.class,
	de.uka.ilkd.key.parser.TestTermParserOCL.class,
	de.uka.ilkd.key.parser.TestTacletParserOCL.class
     };

     static Class[] ruleTests = new Class[] {
	de.uka.ilkd.key.rule.TestSchemaModalOperators.class,
  	de.uka.ilkd.key.rule.TestTacletBuild.class,
  	de.uka.ilkd.key.rule.TestCollisionResolving.class,
  	de.uka.ilkd.key.rule.TestMatchTaclet.class,
        de.uka.ilkd.key.rule.TestApplyTaclet.class,
	de.uka.ilkd.key.rule.TestUpdateSimplifier.class,
	de.uka.ilkd.key.rule.TestOCLTaclets.class,

 	de.uka.ilkd.key.rule.inst.TestGenericSortInstantiations.class,
  	de.uka.ilkd.key.rule.metaconstruct.TestProgramMetaConstructs.class,
 	de.uka.ilkd.key.rule.soundness.TestProofObligationCreation.class
     };


     static Class[] proofConstructionTests = new Class[] {
   	de.uka.ilkd.key.proof.TestTacletIndex.class,
   	de.uka.ilkd.key.proof.TestProofTree.class,
	de.uka.ilkd.key.proof.incclosure.TestMerger.class,
   	de.uka.ilkd.key.proof.TestGoal.class,
	de.uka.ilkd.key.proof.TestTermTacletAppIndex.class
     };


     static Class[] javaTests = new Class[] {
	de.uka.ilkd.key.java.TestTypeConverter.class,
        de.uka.ilkd.key.java.TestJavaInfo.class,
        de.uka.ilkd.key.java.TestJavaCardDLJavaExtensions.class,
  	de.uka.ilkd.key.java.TestRecoder2KeY.class,
 	de.uka.ilkd.key.java.TestKeYRecoderMapping.class,
	de.uka.ilkd.key.java.visitor.TestDeclarationProgramVariableCollector.class,
        de.uka.ilkd.key.java.TestContextStatementBlock.class
     };

     static Class[] logicModelTests = new Class[] {
        de.uka.ilkd.key.logic.TestTermFactory.class,
        de.uka.ilkd.key.logic.TestTerm.class,
        de.uka.ilkd.key.logic.TestNamespace.class,
        de.uka.ilkd.key.logic.TestConstraint.class,
        de.uka.ilkd.key.logic.TestUpdateFactory.class,
        de.uka.ilkd.key.logic.TestUpdatetermNormalisation.class,
   	de.uka.ilkd.key.logic.TestSemisequent.class,
   	de.uka.ilkd.key.logic.TestPosInOcc.class,   	
   	de.uka.ilkd.key.logic.TestClashFreeSubst.class,
  	de.uka.ilkd.key.logic.TestSyntacticalReplaceVisitor.class,
 	de.uka.ilkd.key.logic.TestTermOrdering.class,
	de.uka.ilkd.key.logic.TestVariableNamer.class
     };


     static Class[] gfTests = new Class[] {
	de.uka.ilkd.key.ocl.gf.TestGfAstNode.class,
	de.uka.ilkd.key.ocl.gf.TestUtils.class

     };


     static Class[] speclangTests = new Class[] {
        de.uka.ilkd.key.speclang.jml.translation.TestJMLTranslator.class,
        de.uka.ilkd.key.speclang.ocl.translation.TestOCLTranslator.class,
        de.uka.ilkd.key.speclang.jml.pretranslation.TestJMLPreTranslator.class
      };

     
     public static TestSuite createSuite(Class[] testClasses, final String msg) {
	TestSuite suite = new TestSuite() {
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
	suite.addTest(createSuite(utilityTests, "Testing Utilities and Collections"));
	suite.addTest(createSuite(parserTests, "Testing Parsers"));
	suite.addTest(createSuite(ruleTests, "Testing Rule Engine"));
	suite.addTest(createSuite(proofConstructionTests, "Testing Rule Indexing"));
	suite.addTest(createSuite(javaTests, "Testing Java Datastructures"));
	suite.addTest(createSuite(logicModelTests, "Testing Logic Engine"));
	suite.addTest(createSuite(gfTests, "Testing Grammatical Framework"));
        suite.addTest(createSuite(speclangTests, "Testing JML/OCL support"));
        
	return suite;
    }

    public TestKey(String name) {
	super(name);        
    }

}

