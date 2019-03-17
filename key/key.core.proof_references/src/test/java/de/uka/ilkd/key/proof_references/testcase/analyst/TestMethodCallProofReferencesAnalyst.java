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

package de.uka.ilkd.key.proof_references.testcase.analyst;

import de.uka.ilkd.key.proof_references.analyst.MethodCallProofReferencesAnalyst;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.proof_references.testcase.AbstractProofReferenceTestCase;

/**
 * Tests for {@link MethodCallProofReferencesAnalyst}.
 * @author Martin Hentschel
 */
public class TestMethodCallProofReferencesAnalyst extends AbstractProofReferenceTestCase {
   /**
    * Tests "constructorTest".
    */
   public void testConstructorTest() throws Exception {
      doReferenceMethodTest(TESTCASE_DIRECTORY, 
                            "/proofReferences/constructorTest/ConstructorTest.java", 
                            "ConstructorTest", 
                            "ConstructorTest", 
                            false,
                            new MethodCallProofReferencesAnalyst(),
                            new ExpectedProofReferences(IProofReference.CALL_METHOD, "ConstructorTest::<createObject>"),
                            new ExpectedProofReferences(IProofReference.CALL_METHOD, "ConstructorTest::<allocate>"),
                            new ExpectedProofReferences(IProofReference.CALL_METHOD, "ConstructorTest::<prepareEnter>"),
                            new ExpectedProofReferences(IProofReference.CALL_METHOD, "java.lang.Object::<prepare>"),
                            new ExpectedProofReferences(IProofReference.CALL_METHOD, "java.lang.Object::<init>"),
                            new ExpectedProofReferences(IProofReference.CALL_METHOD, "A::magic"),
                            new ExpectedProofReferences(IProofReference.CALL_METHOD, "B::staticMagic"));
   }
   
   /**
    * Tests "methodCall".
    */
   public void testMethodCall() throws Exception {
      doReferenceMethodTest(TESTCASE_DIRECTORY, 
                            "/proofReferences/methodCall/MethodCall.java", 
                            "methodCall.MethodCall",
                            "caller", 
                            false,
                            new MethodCallProofReferencesAnalyst(),
                            new ExpectedProofReferences(IProofReference.CALL_METHOD, "methodCall.Class::a"));
   }
   
   /**
    * Tests "methodCallSuper".
    */
   public void testMethodCallSuper() throws Exception {
      doReferenceMethodTest(TESTCASE_DIRECTORY, 
                            "/proofReferences/methodCallSuper/MethodCallSuper.java", 
                            "methodCallSuper.MethodCallSuper",
                            "caller", 
                            false,
                            new MethodCallProofReferencesAnalyst(),
                            new ExpectedProofReferences(IProofReference.CALL_METHOD, "methodCallSuper.Super::a"));
   }
   
   /**
    * Tests "methodCallWithAssignment".
    */
   public void testMethodCallWithAssignment() throws Exception {
      doReferenceMethodTest(TESTCASE_DIRECTORY, 
                            "/proofReferences/methodCallWithAssignment/MethodCall.java",
                            "methodCallWithAssignment.MethodCall",
                            "caller", 
                            false,
                            new MethodCallProofReferencesAnalyst(),
                            new ExpectedProofReferences(IProofReference.CALL_METHOD, "methodCallWithAssignment.Class::a"));
   }
   
   /**
    * Tests "methodCallWithAssignmentSuper".
    */
   public void testMethodCallWithAssignmentSuper() throws Exception {
      doReferenceMethodTest(TESTCASE_DIRECTORY, 
                            "/proofReferences/methodCallWithAssignmentSuper/MethodCallWithAssignmentSuper.java",
                            "methodCallWithAssignmentSuper.MethodCallWithAssignmentSuper",
                            "caller", 
                            false,
                            new MethodCallProofReferencesAnalyst(),
                            new ExpectedProofReferences(IProofReference.CALL_METHOD, "methodCallWithAssignmentSuper.Super::a"));
   }
   
   /**
    * Tests "methodCallWithAssignmentWithinClass".
    */
   public void testMethodCallWithAssignmentWithinClass() throws Exception {
      doReferenceMethodTest(TESTCASE_DIRECTORY, 
                            "/proofReferences/methodCallWithAssignmentWithinClass/MethodCallWithAssignmentWithinClass.java", 
                            "methodCallWithAssignmentWithinClass.MethodCallWithAssignmentWithinClass",
                            "caller", 
                            false,
                            new MethodCallProofReferencesAnalyst(),
                            new ExpectedProofReferences(IProofReference.CALL_METHOD, "methodCallWithAssignmentWithinClass.MethodCallWithAssignmentWithinClass::callme"));
   }
   
   /**
    * Tests "methodCallWithinClass".
    */
   public void testMethodCallWithinClass() throws Exception {
      doReferenceMethodTest(TESTCASE_DIRECTORY, 
                            "/proofReferences/methodCallWithinClass/MethodCallWithinClass.java", 
                            "methodCallWithinClass.MethodCallWithinClass",
                            "caller", 
                            false,
                            new MethodCallProofReferencesAnalyst(),
                            new ExpectedProofReferences(IProofReference.CALL_METHOD, "methodCallWithinClass.MethodCallWithinClass::callme"));
   }
   
   /**
    * Tests "staticMethodCall".
    */
   public void testStaticMethodCall() throws Exception {
      doReferenceMethodTest(TESTCASE_DIRECTORY, 
                            "/proofReferences/staticMethodCall/StaticMethodCall.java", 
                            "staticMethodCall.StaticMethodCall",
                            "caller", 
                            false,
                            new MethodCallProofReferencesAnalyst(),
                            new ExpectedProofReferences(IProofReference.CALL_METHOD, "staticMethodCall.StaticClass::callMe"));
   }
   
   /**
    * Tests "staticMethodCallStaticViaTypereference".
    */
   public void testStaticMethodCallStaticViaTypereference() throws Exception {
      doReferenceMethodTest(TESTCASE_DIRECTORY, 
                            "/proofReferences/staticMethodCallStaticViaTypereference/StaticMethodCallStaticViaTypereference.java", 
                            "staticMethodCallStaticViaTypereference.StaticMethodCallStaticViaTypereference",
                            "caller",
                            false,
                            new MethodCallProofReferencesAnalyst(),
                            new ExpectedProofReferences(IProofReference.CALL_METHOD, "staticMethodCallStaticViaTypereference.StaticClass::callMe"));
   }
   
   /**
    * Tests "staticMethodCallStaticWithAssignmentViaTypereference".
    */
   public void testStaticMethodCallStaticWithAssignmentViaTypereference() throws Exception {
      doReferenceMethodTest(TESTCASE_DIRECTORY, 
                            "/proofReferences/staticMethodCallStaticWithAssignmentViaTypereference/StaticMethodCallStaticWithAssignmentViaTypereference.java", 
                            "staticMethodCallStaticWithAssignmentViaTypereference.StaticMethodCallStaticWithAssignmentViaTypereference",
                            "caller", 
                            false,
                            new MethodCallProofReferencesAnalyst(),
                            new ExpectedProofReferences(IProofReference.CALL_METHOD, "staticMethodCallStaticWithAssignmentViaTypereference.StaticClass::callMe"));
   }
}