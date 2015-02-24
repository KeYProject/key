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