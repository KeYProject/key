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

package org.key_project.sed.ui.visualization.execution_tree.feature;

import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.ICreateFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.ISEDOperationContract;
import org.key_project.sed.core.model.memory.SEDMemoryOperationContract;
import org.key_project.sed.ui.visualization.execution_tree.provider.IExecutionTreeImageConstants;

/**
 * Implementation of {@link ICreateFeature} for {@link ISEDOperationContract}s.
 * @author Martin Hentschel
 */
public class OperationContractCreateFeature extends AbstractDebugNodeCreateFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IAddFeature}.
    */
   public OperationContractCreateFeature(IFeatureProvider fp) {
       super(fp, "Operation Contract", "Create a new Operation Contract");
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getCreateImageId() {
      return IExecutionTreeImageConstants.IMG_OPERATION_CONTRACT;
   }

   /**
    * {@inheritDoc}
    */   
   @Override
   public String getNodeType() {
      return "Operation Contract";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected ISEDDebugNode createNewDebugNode(ISEDDebugTarget target,
                                              ISEDDebugNode parent,
                                              ISEDThread thread,
                                              String name) throws DebugException {
      SEDMemoryOperationContract result = new SEDMemoryOperationContract(target, parent, thread);
      result.setName(name);
      return result;
   }
}