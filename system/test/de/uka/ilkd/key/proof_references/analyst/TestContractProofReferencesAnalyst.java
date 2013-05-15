package de.uka.ilkd.key.proof_references.analyst;

import de.uka.ilkd.key.proof_references.AbstractProofReferenceTestCase;
import de.uka.ilkd.key.proof_references.reference.IProofReference;

/**
 * Tests for {@link ContractProofReferencesAnalyst}.
 * @author Martin Hentschel
 */
public class TestContractProofReferencesAnalyst extends AbstractProofReferenceTestCase {
   /**
    * Tests "UseOperationContractTest".
    */
   public void testUseOperationContracts() throws Exception {
      doReferenceMethodTest(keyRepDirectory, 
                            "examples/_testcase/proofReferences/UseOperationContractTest/UseOperationContractTest.java", 
                            "UseOperationContractTest", 
                            "main", 
                            true,
                            new ContractProofReferencesAnalyst(),
                            new ExpectedProofReferences(IProofReference.USE_CONTRACT, "pre: {heap=java.lang.Object::<inv>(heap,self)}; mby: null; post: {heap=and(imp(equals(exc,null),and(equals(result,Z(2(4(#)))),java.lang.Object::<inv>(heap,self))),equals(exc,null))}; mods: {heap=allLocs, savedHeap=null}; hasMod: true; termination: diamond; transaction: false"));
   }
}
