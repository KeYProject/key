package de.uka.ilkd.key.proof_references.analyst;

import de.uka.ilkd.key.proof_references.AbstractProofReferenceTestCase;
import de.uka.ilkd.key.proof_references.reference.IProofReference;

/**
 * Tests for {@link MethodBodyExpandProofReferencesAnalyst}.
 * @author Martin Hentschel
 */
public class TestMethodBodyExpandProofReferencesAnalyst extends AbstractProofReferenceTestCase {
   /**
    * Tests "MethodBodyExpand".
    */
   public void testMethodBodyExpand() throws Exception {
      doReferenceMethodTest(keyRepDirectory, 
                            "examples/_testcase/proofReferences/MethodBodyExpand/MethodBodyExpand.java", 
                            "MethodBodyExpand", 
                            "main", 
                            false,
                            new MethodBodyExpandProofReferencesAnalyst(),
                            new ExpectedProofReferences(IProofReference.INLINE_METHOD, "MethodBodyExpand::main"), 
                            new ExpectedProofReferences(IProofReference.INLINE_METHOD, "MethodBodyExpand::magic42"));
   }
}
