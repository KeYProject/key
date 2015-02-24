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
                            new ExpectedProofReferences(IProofReference.USE_CONTRACT, "pre: {heap=java.lang.Object::<inv>(heap,self)}; mby: null; post: {heap=and(and(equals(result,Z(2(4(#)))),java.lang.Object::<inv>(heap,self)),equals(exc,null))}; mods: {heap=allLocs, savedHeap=null}; hasMod: {heap=true, savedHeap=true}; termination: diamond; transaction: false"));
   }
}