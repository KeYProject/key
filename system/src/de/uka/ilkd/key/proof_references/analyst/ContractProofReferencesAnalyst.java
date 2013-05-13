package de.uka.ilkd.key.proof_references.analyst;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof_references.ProofReferenceUtil;
import de.uka.ilkd.key.proof_references.reference.DefaultProofReference;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.rule.AbstractContractRuleApp;
import de.uka.ilkd.key.speclang.Contract;

/**
 * Extracts {@link ContractProofReference}s.
 * @author Martin Hentschel
 */
public class ContractProofReferencesAnalyst implements IProofReferencesAnalyst {
   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableList<IProofReference<?>> computeReferences(Node node, Services services) {
      if (node.getAppliedRuleApp() instanceof AbstractContractRuleApp) {
         AbstractContractRuleApp contractRuleApp = (AbstractContractRuleApp)node.getAppliedRuleApp();
         DefaultProofReference<Contract> reference = new DefaultProofReference<Contract>(ProofReferenceUtil.USE_CONTRACT, node, contractRuleApp.getInstantiation());
         return ImmutableSLList.<IProofReference<?>>nil().append(reference);
      }
      else {
         return null;
      }
   }
}
