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

import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDUseOperationContract;
import org.key_project.sed.ui.visualization.execution_tree.provider.IExecutionTreeImageConstants;

/**
 * Implementation of {@link IAddFeature} for {@link ISEDUseOperationContract}s.
 * @author Martin Hentschel
 */
public class UseOperationContractAddFeature extends AbstractDebugNodeAddFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IAddFeature}.
    */
   public UseOperationContractAddFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean canAddBusinessObject(Object businessObject) {
      return businessObject instanceof ISEDUseOperationContract;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getImageId(ISEDDebugNode node) {
      ISEDUseOperationContract contractNode = (ISEDUseOperationContract)node;
      if (contractNode.isPreconditionComplied()) {
         if (!contractNode.hasNotNullCheck() || contractNode.isNotNullCheckComplied()) {
            return IExecutionTreeImageConstants.IMG_USE_OPERATION_CONTRACT;
         }
         else {
            return IExecutionTreeImageConstants.IMG_USE_OPERATION_CONTRACT_NOT_NPC;
         }
      }
      else {
         if (!contractNode.hasNotNullCheck() || contractNode.isNotNullCheckComplied()) {
            return IExecutionTreeImageConstants.IMG_USE_OPERATION_CONTRACT_NOT_PRE;
         }
         else {
            return IExecutionTreeImageConstants.IMG_USE_OPERATION_CONTRACT_NOT_PRE_NOT_NPC;
         }
      }
   }
}