package de.uka.ilkd.key.proof_references.analyst;

import de.uka.ilkd.key.proof_references.AbstractProofReferenceTestCase;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.symbolic_execution.util.IFilter;

/**
 * Tests for {@link ClassAxiomAndInvariantProofReferencesAnalyst}.
 * @author Martin Hentschel
 */
public class TestClassAxiomAndInvariantProofReferencesAnalyst extends AbstractProofReferenceTestCase {
   /**
    * Tests "InvariantInOperationContract".
    */
   public void testInvariantInOperationContract() throws Exception {
      doReferenceMethodTest(keyRepDirectory, 
                            "examples/_testcase/proofReferences/InvariantInOperationContract/InvariantInOperationContract.java", 
                            "InvariantInOperationContract", 
                            "main", 
                            false,
                            new ClassAxiomAndInvariantProofReferencesAnalyst(),
                            new IFilter<IProofReference<?>>() {
                              @Override
                              public boolean select(IProofReference<?> element) {
                                 return IProofReference.USE_AXIOM.equals(element.getKind());
                              }
                            },
                            new ExpectedProofReferences(IProofReference.USE_AXIOM, "equiv(java.lang.Object::<inv>(heap,self),not(equals(Child::select(heap,self,InvariantInOperationContract::$child),null)))"));
   }
   
   /**
    * Tests "NestedInvariantInOperationContract".
    */
   public void testNestedInvariantInOperationContract() throws Exception {
      doReferenceMethodTest(keyRepDirectory, 
                            "examples/_testcase/proofReferences/NestedInvariantInOperationContract/NestedInvariantInOperationContract.java", 
                            "NestedInvariantInOperationContract", 
                            "main", 
                            false,
                            new ClassAxiomAndInvariantProofReferencesAnalyst(),
                            new IFilter<IProofReference<?>>() {
                               @Override
                               public boolean select(IProofReference<?> element) {
                                  return IProofReference.USE_AXIOM.equals(element.getKind());
                               }
                             },
                            new ExpectedProofReferences(IProofReference.USE_AXIOM, "equiv(java.lang.Object::<inv>(heap,self),not(equals(ChildContainer::select(heap,self,NestedInvariantInOperationContract::$cc),null)))"));
   }
   
   /**
    * Tests "ModelFieldTest#doubleX".
    */
   public void testModelFieldTest_doubleX() throws Exception {
      doReferenceMethodTest(keyRepDirectory, 
                            "examples/_testcase/proofReferences/ModelFieldTest/ModelFieldTest.java", 
                            "ModelFieldTest", 
                            "doubleX", 
                            false,
                            new ClassAxiomAndInvariantProofReferencesAnalyst(),
                            new ExpectedProofReferences(IProofReference.USE_AXIOM, "equiv(java.lang.Object::<inv>(heap,self),true)"),
                            new ExpectedProofReferences(IProofReference.USE_AXIOM, "equals(test.ModelFieldTest::$f(heap,self),javaMulInt(Z(2(#)),int::select(heap,self,test.ModelFieldTest::$x)))"));
   }
   
   /**
    * Tests "ModelFieldTest#test.ModelFieldTest::$f".
    */
   public void testModelFieldTest_f() throws Exception {
      doReferenceFunctionTest(keyRepDirectory, 
                              "examples/_testcase/proofReferences/ModelFieldTest/ModelFieldTest.java", 
                              "ModelFieldTest", 
                              "test.ModelFieldTest::$f", 
                              false,
                              new ClassAxiomAndInvariantProofReferencesAnalyst(),
                              new ExpectedProofReferences(IProofReference.USE_AXIOM, "equiv(java.lang.Object::<inv>(heap,self),true)"),
                              new ExpectedProofReferences(IProofReference.USE_AXIOM, "equals(test.ModelFieldTest::$f(heap,self),javaMulInt(Z(2(#)),int::select(heap,self,test.ModelFieldTest::$x)))"));
   }
   
   /**
    * Tests "AccessibleTest".
    */
   public void testAccessibleTest() throws Exception {
      doReferenceFunctionTest(keyRepDirectory, 
                              "examples/_testcase/proofReferences/AccessibleTest/AccessibleTest.java", 
                              "B", 
                              "java.lang.Object::<inv>", 
                              false,
                              new ClassAxiomAndInvariantProofReferencesAnalyst(),
                              new ExpectedProofReferences(IProofReference.USE_AXIOM, "equiv(java.lang.Object::<inv>(heap,self),java.lang.Object::<inv>(heap,test.AccessibleTest::select(heap,self,test.B::$c)))"),
                              new ExpectedProofReferences(IProofReference.USE_INVARIANT, "java.lang.Object::<inv>(heap,test.AccessibleTest::select(heap,self,test.B::$c))"));
   }
}
