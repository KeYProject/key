/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package de.hentschel.visualdbc.datasource.key.rule;

import java.util.LinkedList;
import java.util.List;

import de.hentschel.visualdbc.datasource.key.model.KeyConnection;
import de.hentschel.visualdbc.datasource.model.IDSOperationContract;
import de.hentschel.visualdbc.datasource.model.IDSProvableReference;
import de.hentschel.visualdbc.datasource.model.memory.MemoryProvableReference;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.proof.mgt.RuleJustificationBySpec;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.speclang.Contract;

/**
 * Implementation of {@link IRuleAnalyst} for rule: Use Operation Contract
 * @author Martin Hentschel
 */
public class UseOperationContractRuleAnalyst implements IRuleAnalyst {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canHandle(KeyConnection connection, Services services, Node node) {
      return node != null && KeyProofReferenceUtil.USE_OPERATION_CONTRACT.equals(node.name());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<IDSProvableReference> getReferences(KeyConnection connection, Services services, Node node) {
      List<IDSProvableReference> result = new LinkedList<IDSProvableReference>();
      // See: ProofSaver#save() and SpecificationRepository#drawGraph(Proof)
      if (node != null && node.getAppliedRuleApp() instanceof IBuiltInRuleApp) {
         IBuiltInRuleApp app = (IBuiltInRuleApp)node.getAppliedRuleApp();
         if (app.rule() instanceof UseOperationContractRule) {
            RuleJustification ruleJusti = node.proof().env().getJustifInfo().getJustification(app, node.proof().getServices());
            if (ruleJusti instanceof RuleJustificationBySpec) {
               RuleJustificationBySpec spec = (RuleJustificationBySpec)ruleJusti;
               Contract usedSpec = spec.getSpec();
               // Add references to used operation contract
               ImmutableSet<Contract> atomicContracts = services.getSpecificationRepository().splitContract(usedSpec);
               for (Contract atomicContract : atomicContracts) {
                  IDSOperationContract dsContract = connection.getOperationContract(atomicContract);
                  if (dsContract != null) {
                     result.add(new MemoryProvableReference(dsContract, KeyProofReferenceUtil.USE_OPERATION_CONTRACT));
                  }
               }
            }
         }
      }
      return result;
   }
}
