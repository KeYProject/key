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

import java.util.LinkedHashSet;

import org.eclipse.core.runtime.Assert;

import de.hentschel.visualdbc.datasource.key.model.KeyConnection;
import de.hentschel.visualdbc.datasource.model.IDSAttribute;
import de.hentschel.visualdbc.datasource.model.IDSAxiom;
import de.hentschel.visualdbc.datasource.model.IDSEnumLiteral;
import de.hentschel.visualdbc.datasource.model.IDSInvariant;
import de.hentschel.visualdbc.datasource.model.IDSOperation;
import de.hentschel.visualdbc.datasource.model.IDSOperationContract;
import de.hentschel.visualdbc.datasource.model.IDSProvableReference;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.model.memory.MemoryProvableReference;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.declaration.EnumClassDeclaration;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof_references.ProofReferenceUtil;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.ClassInvariant;
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
   public LinkedHashSet<IDSProvableReference> getReferences(KeyConnection connection, Services services, Node node) throws DSException {
      LinkedHashSet<IDSProvableReference> result = new LinkedHashSet<IDSProvableReference>();
      LinkedHashSet<IProofReference<?>> references = ProofReferenceUtil.computeProofReferences(node, node.proof().getServices());
      for (IProofReference<?> reference : references) {
         if (IProofReference.INLINE_METHOD.equals(reference.getKind())) {
            Assert.isTrue(reference.getTarget() instanceof IProgramMethod);
            IDSOperation operation = connection.getOperation((IProgramMethod)reference.getTarget());
            if (operation != null) {
               result.add(new MemoryProvableReference(operation, KeyProofReferenceUtil.INLINE_METHOD));
            }
         }
         else if (IProofReference.CALL_METHOD.equals(reference.getKind())) {
            Assert.isTrue(reference.getTarget() instanceof IProgramMethod);
            IDSOperation operation = connection.getOperation((IProgramMethod)reference.getTarget());
            if (operation != null) {
               result.add(new MemoryProvableReference(operation, KeyProofReferenceUtil.CALL_METHOD));
            }
         }
         else if (IProofReference.USE_CONTRACT.equals(reference.getKind())) {
            Assert.isTrue(reference.getTarget() instanceof Contract);
            IDSOperationContract contract = connection.getOperationContract((Contract)reference.getTarget());
            if (contract != null) {
               result.add(new MemoryProvableReference(contract, KeyProofReferenceUtil.USE_CONTRACT));
            }
         }
         else if (IProofReference.ACCESS.equals(reference.getKind())) {
            Assert.isTrue(reference.getTarget() instanceof IProgramVariable);
            IProgramVariable target = (IProgramVariable)reference.getTarget();
            if (EnumClassDeclaration.isEnumConstant(target)) {
               IDSEnumLiteral literal = connection.getEnumLiteral(target);
               if (literal != null) {
                  result.add(new MemoryProvableReference(literal, KeyProofReferenceUtil.ACCESS));
               }
            }
            else {
               IDSAttribute attribute = connection.getAttribute(target);
               if (attribute != null) {
                  result.add(new MemoryProvableReference(attribute, KeyProofReferenceUtil.ACCESS));
               }
            }
         }
         else if (IProofReference.USE_INVARIANT.equals(reference.getKind())) {
            Assert.isTrue(reference.getTarget() instanceof ClassInvariant);
            IDSInvariant invariant = connection.getInvariant((ClassInvariant)reference.getTarget());
            if (invariant != null) {
               result.add(new MemoryProvableReference(invariant, KeyProofReferenceUtil.USE_INVARIANT));
            }
         }
         else if (IProofReference.USE_AXIOM.equals(reference.getKind())) {
            Assert.isTrue(reference.getTarget() instanceof ClassAxiom);
            IDSAxiom axiom = connection.getAxiom((ClassAxiom)reference.getTarget());
            if (axiom != null) {
               result.add(new MemoryProvableReference(axiom, KeyProofReferenceUtil.USE_AXIOM));
            }
         }
         else {
            throw new DSException("Unsupported proof reference \"" + reference + "\".");
         }
      }
      return result;
   }
}