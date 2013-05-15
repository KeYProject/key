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
