/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof_references.testcase.analyst;

import de.uka.ilkd.key.proof_references.analyst.ContractProofReferencesAnalyst;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.proof_references.testcase.AbstractProofReferenceTestCase;

import org.junit.jupiter.api.Test;

/**
 * Tests for {@link ContractProofReferencesAnalyst}.
 *
 * @author Martin Hentschel
 */
public class TestContractProofReferencesAnalyst extends AbstractProofReferenceTestCase {
    /**
     * Tests "UseOperationContractTest".
     */
    @Test
    public void testUseOperationContracts() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/UseOperationContractTest/UseOperationContractTest.java",
            "UseOperationContractTest", "main", true, new ContractProofReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.USE_CONTRACT,
                "pre: {heap=java.lang.Object::<inv>(heap,self)<<impl>>}; mby: null; post: {heap=and(and(equals(result_magic42,Z(2(4(#))))<<origin(ensures @ file UseOperationContractTest.java @ line 12) ([])>>,java.lang.Object::<inv>(heap,self)<<impl>>)<<SC>>,equals(exc<<origin(ensures (implicit)) ([])>>,null)<<impl, origin(ensures (implicit)) ([])>>)}; mods: {heap=allLocs, savedHeap=null}; hasMod: {heap=true, savedHeap=true}; termination: diamond; transaction: false"));
    }
}
