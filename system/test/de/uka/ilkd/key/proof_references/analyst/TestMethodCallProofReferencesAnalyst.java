package de.uka.ilkd.key.proof_references.analyst;

import de.uka.ilkd.key.proof_references.AbstractProofReferenceTestCase;
import de.uka.ilkd.key.proof_references.reference.IProofReference;

/**
 * Tests for {@link MethodCallProofReferencesAnalyst}.
 * @author Martin Hentschel
 */
public class TestMethodCallProofReferencesAnalyst extends AbstractProofReferenceTestCase {
   /**
    * Tests "methodCall".
    */
   public void testMethodCall() throws Exception {
      doReferenceMethodTest(keyRepDirectory, 
                            "examples/_testcase/proofReferences/methodCall/MethodCall.java", 
                            "MethodCall", 
                            "caller", 
                            false,
                            new MethodCallProofReferencesAnalyst(),
                            new ExpectedProofReferences(IProofReference.CALL_METHOD, "methodCall.Class::a"));
   }
   
   /**
    * Tests "methodCallSuper".
    */
   public void testMethodCallSuper() throws Exception {
      doReferenceMethodTest(keyRepDirectory, 
                            "examples/_testcase/proofReferences/methodCallSuper/MethodCallSuper.java", 
                            "MethodCallSuper", 
                            "caller", 
                            false,
                            new MethodCallProofReferencesAnalyst(),
                            new ExpectedProofReferences(IProofReference.CALL_METHOD, "methodCallSuper.Super::a"));
   }
   
   /**
    * Tests "methodCallWithAssignment".
    */
   public void testMethodCallWithAssignment() throws Exception {
      doReferenceMethodTest(keyRepDirectory, 
                            "examples/_testcase/proofReferences/methodCallWithAssignment/MethodCall.java", 
                            "MethodCall", 
                            "caller", 
                            false,
                            new MethodCallProofReferencesAnalyst(),
                            new ExpectedProofReferences(IProofReference.CALL_METHOD, "methodCallWithAssignment.Class::a"));
   }
   
   /**
    * Tests "methodCallWithAssignmentSuper".
    */
   public void testMethodCallWithAssignmentSuper() throws Exception {
      doReferenceMethodTest(keyRepDirectory, 
                            "examples/_testcase/proofReferences/methodCallWithAssignmentSuper/MethodCallWithAssignmentSuper.java", 
                            "MethodCallWithAssignmentSuper", 
                            "caller", 
                            false,
                            new MethodCallProofReferencesAnalyst(),
                            new ExpectedProofReferences(IProofReference.CALL_METHOD, "methodCallWithAssignmentSuper.Super::a"));
   }
   
   /**
    * Tests "methodCallWithAssignmentWithinClass".
    */
   public void testMethodCallWithAssignmentWithinClass() throws Exception {
      doReferenceMethodTest(keyRepDirectory, 
                            "examples/_testcase/proofReferences/methodCallWithAssignmentWithinClass/MethodCallWithAssignmentWithinClass.java", 
                            "MethodCallWithAssignmentWithinClass", 
                            "caller", 
                            false,
                            new MethodCallProofReferencesAnalyst(),
                            new ExpectedProofReferences(IProofReference.CALL_METHOD, "methodCallWithAssignmentWithinClass.MethodCallWithAssignmentWithinClass::callme"));
   }
   
   /**
    * Tests "methodCallWithinClass".
    */
   public void testMethodCallWithinClass() throws Exception {
      doReferenceMethodTest(keyRepDirectory, 
                            "examples/_testcase/proofReferences/methodCallWithinClass/MethodCallWithinClass.java", 
                            "MethodCallWithinClass", 
                            "caller", 
                            false,
                            new MethodCallProofReferencesAnalyst(),
                            new ExpectedProofReferences(IProofReference.CALL_METHOD, "methodCallWithinClass.MethodCallWithinClass::callme"));
   }
   
   /**
    * Tests "staticMethodCall".
    */
   public void testStaticMethodCall() throws Exception {
      doReferenceMethodTest(keyRepDirectory, 
                            "examples/_testcase/proofReferences/staticMethodCall/StaticMethodCall.java", 
                            "StaticMethodCall", 
                            "caller", 
                            false,
                            new MethodCallProofReferencesAnalyst(),
                            new ExpectedProofReferences(IProofReference.CALL_METHOD, "staticMethodCall.StaticClass::callMe"));
   }
   
   /**
    * Tests "staticMethodCallStaticViaTypereference".
    */
   public void testStaticMethodCallStaticViaTypereference() throws Exception {
      doReferenceMethodTest(keyRepDirectory, 
                            "examples/_testcase/proofReferences/staticMethodCallStaticViaTypereference/StaticMethodCallStaticViaTypereference.java", 
                            "StaticMethodCallStaticViaTypereference", 
                            "caller", 
                            false,
                            new MethodCallProofReferencesAnalyst(),
                            new ExpectedProofReferences(IProofReference.CALL_METHOD, "staticMethodCallStaticViaTypereference.StaticClass::callMe"));
   }
   
   /**
    * Tests "staticMethodCallStaticWithAssignmentViaTypereference".
    */
   public void testStaticMethodCallStaticWithAssignmentViaTypereference() throws Exception {
      doReferenceMethodTest(keyRepDirectory, 
                            "examples/_testcase/proofReferences/staticMethodCallStaticWithAssignmentViaTypereference/StaticMethodCallStaticWithAssignmentViaTypereference.java", 
                            "StaticMethodCallStaticWithAssignmentViaTypereference", 
                            "caller", 
                            false,
                            new MethodCallProofReferencesAnalyst(),
                            new ExpectedProofReferences(IProofReference.CALL_METHOD, "staticMethodCallStaticWithAssignmentViaTypereference.StaticClass::callMe"));
   }
}
