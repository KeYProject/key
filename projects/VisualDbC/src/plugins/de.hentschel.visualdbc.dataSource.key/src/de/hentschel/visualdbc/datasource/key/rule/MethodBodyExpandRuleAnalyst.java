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

import org.eclipse.core.runtime.Assert;

import de.hentschel.visualdbc.datasource.key.model.KeyConnection;
import de.hentschel.visualdbc.datasource.model.IDSOperation;
import de.hentschel.visualdbc.datasource.model.IDSProvableReference;
import de.hentschel.visualdbc.datasource.model.memory.MemoryProvableReference;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;

/**
 * Implementation of {@link IRuleAnalyst} for rule: methodBodyExpand
 * @author Martin Hentschel
 */
public class MethodBodyExpandRuleAnalyst implements IRuleAnalyst {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canHandle(KeyConnection connection, Services services, Node node) {
      return node != null && 
             node.getNodeInfo() != null && 
             node.getNodeInfo().getActiveStatement() instanceof MethodBodyStatement;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<IDSProvableReference> getReferences(KeyConnection connection, Services services, Node node) {
      List<IDSProvableReference> result = new LinkedList<IDSProvableReference>();
      // Get node info
      NodeInfo info = node.getNodeInfo();
      Assert.isNotNull(info);
      // Get active statement
      Assert.isTrue(info.getActiveStatement() instanceof MethodBodyStatement);
      MethodBodyStatement mbs = (MethodBodyStatement)info.getActiveStatement();
      // Get referenced program method.
      IProgramMethod pm = mbs.getProgramMethod(services);
      // Get data source instance
      IDSOperation operation = connection.getOperation(pm);
      if (operation != null) {
         result.add(new MemoryProvableReference(operation, KeyProofReferenceUtil.METHOD_BODY_EXPAND));
      }
      return result;
   }
}
