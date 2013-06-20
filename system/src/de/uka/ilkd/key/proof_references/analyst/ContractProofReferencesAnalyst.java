// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof_references.analyst;

import java.util.LinkedHashSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof_references.reference.DefaultProofReference;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.rule.AbstractContractRuleApp;
import de.uka.ilkd.key.speclang.Contract;

/**
 * Extracts used contracts.
 * @author Martin Hentschel
 */
public class ContractProofReferencesAnalyst implements IProofReferencesAnalyst {
   /**
    * {@inheritDoc}
    */
   @Override
   public LinkedHashSet<IProofReference<?>> computeReferences(Node node, Services services) {
      if (node.getAppliedRuleApp() instanceof AbstractContractRuleApp) {
         AbstractContractRuleApp contractRuleApp = (AbstractContractRuleApp)node.getAppliedRuleApp();
         DefaultProofReference<Contract> reference = new DefaultProofReference<Contract>(IProofReference.USE_CONTRACT, node, contractRuleApp.getInstantiation());
         LinkedHashSet<IProofReference<?>> result = new LinkedHashSet<IProofReference<?>>();
         result.add(reference);
         return result;
      }
      else {
         return null;
      }
   }
}