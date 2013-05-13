/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package de.hentschel.visualdbc.datasource.key.rule;

import org.eclipse.core.runtime.Assert;

import de.hentschel.visualdbc.datasource.key.model.KeyConnection;
import de.hentschel.visualdbc.datasource.model.IDSOperation;
import de.hentschel.visualdbc.datasource.model.IDSOperationContract;
import de.hentschel.visualdbc.datasource.model.IDSProvableReference;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.model.memory.MemoryProvableReference;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof_references.ProofReferenceUtil;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.speclang.Contract;

/**
 * Implementation of {@link IRuleAnalyst} which extracts the references
 * with help of KeY's {@link ProofReferenceUtil}.
 * @author Martin Hentschel
 */
public class DefaultRuleAnalyst implements IRuleAnalyst {
   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableList<IDSProvableReference> getReferences(KeyConnection connection, Services services, Node node) throws DSException {
      ImmutableList<IDSProvableReference> result = ImmutableSLList.nil();
      ImmutableList<IProofReference<?>> references = ProofReferenceUtil.computeProofReferences(node, node.proof().getServices());
      for (IProofReference<?> reference : references) {
         if (IProofReference.INLINE_METHOD.equals(reference.getKind())) {
            Assert.isTrue(reference.getTarget() instanceof IProgramMethod);
            IDSOperation operation = connection.getOperation((IProgramMethod)reference.getTarget());
            if (operation != null) {
               result = result.append(new MemoryProvableReference(operation, KeyProofReferenceUtil.INLINE_METHOD));
            }
         }
         else if (IProofReference.CALL_METHOD.equals(reference.getKind())) {
            Assert.isTrue(reference.getTarget() instanceof IProgramMethod);
            IDSOperation operation = connection.getOperation((IProgramMethod)reference.getTarget());
            if (operation != null) {
               result = result.append(new MemoryProvableReference(operation, KeyProofReferenceUtil.CALL_METHOD));
            }
         }
         else if (IProofReference.USE_CONTRACT.equals(reference.getKind())) {
            Assert.isTrue(reference.getTarget() instanceof Contract);
            IDSOperationContract contract = connection.getOperationContract((Contract)reference.getTarget());
            if (contract != null) {
               result = result.append(new MemoryProvableReference(contract, KeyProofReferenceUtil.USE_CONTRACT));
            }
         }
         else {
            throw new DSException("Unsupported proof reference \"" + reference + "\".");
         }
      }
      return result;
   }
}