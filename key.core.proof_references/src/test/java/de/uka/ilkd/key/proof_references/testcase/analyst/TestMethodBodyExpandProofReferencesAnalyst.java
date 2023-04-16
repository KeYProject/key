package de.uka.ilkd.key.proof_references.testcase.analyst;

import de.uka.ilkd.key.proof_references.analyst.MethodBodyExpandProofReferencesAnalyst;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.proof_references.testcase.AbstractProofReferenceTestCase;

import org.junit.jupiter.api.Test;

/**
 * Tests for {@link MethodBodyExpandProofReferencesAnalyst}.
 *
 * @author Martin Hentschel
 */
public class TestMethodBodyExpandProofReferencesAnalyst extends AbstractProofReferenceTestCase {
    /**
     * Tests "MethodBodyExpand".
     */
    @Test
    public void testMethodBodyExpand() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/MethodBodyExpand/MethodBodyExpand.java", "MethodBodyExpand", "main",
            false, new MethodBodyExpandProofReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.INLINE_METHOD, "MethodBodyExpand::main"),
            new ExpectedProofReferences(IProofReference.INLINE_METHOD,
                "MethodBodyExpand::magic42"));
    }
}
