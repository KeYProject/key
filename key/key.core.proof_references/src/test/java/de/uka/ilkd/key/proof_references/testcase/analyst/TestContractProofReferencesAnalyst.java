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

import de.uka.ilkd.key.proof_references.analyst.ContractProofReferencesAnalyst;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.proof_references.testcase.AbstractProofReferenceTestCase;

/**
 * Tests for {@link ContractProofReferencesAnalyst}.
 * @author Martin Hentschel
 */
public class TestContractProofReferencesAnalyst extends AbstractProofReferenceTestCase {
   /**
    * Tests "UseOperationContractTest".
    */
   public void testUseOperationContracts() throws Exception {
      doReferenceMethodTest(TESTCASE_DIRECTORY,
                            "/proofReferences/UseOperationContractTest/UseOperationContractTest.java",
                            "UseOperationContractTest",
                            "main",
                            true,
                            new ContractProofReferencesAnalyst(),
                            new ExpectedProofReferences(IProofReference.USE_CONTRACT, "pre: {heap=java.lang.Object::<inv>(heap,self)<<impl>>}; mby: null; post: {heap=and(and(equals(result<<origin(ensures @ file UseOperationContractTest.java @ line 12) ([])>>,Z(2(4(#))))<<origin(ensures @ file UseOperationContractTest.java @ line 12) ([])>>,java.lang.Object::<inv>(heap,self)<<impl>>)<<SC>>,equals(exc<<origin(ensures (implicit)) ([])>>,null)<<impl, origin(ensures (implicit)) ([])>>)}; mods: {heap=allLocs, savedHeap=null}; hasMod: {heap=true, savedHeap=true}; termination: diamond; transaction: false"));
   }
}
