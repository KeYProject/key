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

package org.key_project.sed.key.ui.visualization.execution_tree.feature;

import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.ICustomContext;
import org.eclipse.graphiti.features.custom.AbstractCustomFeature;
import org.eclipse.graphiti.features.custom.ICustomFeature;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.key.core.model.IKeYSEDDebugNode;
import org.key_project.sed.key.ui.visualization.execution_tree.command.VisualizeConfigurationsCommand;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * An {@link ICustomFeature} which executes 
 * {@link VisualizeConfigurationsCommand#visualizeConfigurations(ISEDDebugNode, org.eclipse.ui.IWorkbenchPage)}
 * on selected business objects.
 * @author Martin Hentschel
 */
public class DebugNodeVisualizeConfigurationsFeature extends AbstractCustomFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} to use.
    */
   public DebugNodeVisualizeConfigurationsFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canExecute(ICustomContext context) {
      try {
         boolean canExecute = false;
         PictogramElement[] pes = context.getPictogramElements();
         if (pes != null) {
            int i = 0;
            while (i < pes.length && !canExecute) {
               Object businessObject = getBusinessObjectForPictogramElement(pes[i]);
               canExecute = VisualizeConfigurationsCommand.canVisualize(businessObject);
               i++;
            }
         }
         return canExecute;
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
         return false;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void execute(ICustomContext context) {
      try {
         PictogramElement[] pes = context.getPictogramElements();
         if (pes != null) {
            for (PictogramElement pe : pes) {
               Object businessObject = getBusinessObjectForPictogramElement(pe);
               if (VisualizeConfigurationsCommand.canVisualize(businessObject)) {
                  VisualizeConfigurationsCommand.visualizeConfigurations((IKeYSEDDebugNode<?>)businessObject, WorkbenchUtil.getActivePage());
               }
            }
         }
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
      }
   }
}