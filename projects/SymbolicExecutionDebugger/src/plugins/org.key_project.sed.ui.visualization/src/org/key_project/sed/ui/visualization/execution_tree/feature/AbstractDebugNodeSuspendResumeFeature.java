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

import java.util.LinkedList;
import java.util.List;

import org.eclipse.debug.core.commands.IDebugCommandHandler;
import org.eclipse.debug.core.commands.IDebugCommandRequest;
import org.eclipse.debug.core.model.ISuspendResume;
import org.eclipse.debug.internal.ui.commands.actions.ExecuteActionRequest;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.ICustomContext;
import org.eclipse.graphiti.features.custom.AbstractCustomFeature;
import org.eclipse.graphiti.features.custom.ICustomFeature;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;

/**
 * An {@link ICustomFeature} which provides the basic functionality to
 * work with {@link ISuspendResume} business objects.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public abstract class AbstractDebugNodeSuspendResumeFeature extends AbstractCustomFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} to use.
    */
   public AbstractDebugNodeSuspendResumeFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canExecute(ICustomContext context) {
      boolean canExecute = false;
      PictogramElement[] pes = context.getPictogramElements();
      if (pes != null) {
         int i = 0;
         while (i < pes.length && !canExecute) {
            Object businessObject = getBusinessObjectForPictogramElement(pes[i]);
            if (businessObject instanceof ISuspendResume) {
               canExecute = canExecute((ISuspendResume)businessObject);
            }
            i++;
         }
      }
      return canExecute;
   }
   
   /**
    * Checks if the execution on the given {@link ISuspendResume} is allowed.
    * @param suspendResume The {@link ISuspendResume} to check.
    * @return {@code true} can execute, {@code false} can not execute.
    */
   protected abstract boolean canExecute(ISuspendResume suspendResume);

   /**
    * {@inheritDoc}
    */
   @Override
   public void execute(ICustomContext context) {
      // Collect business objects
      List<Object> businessObjects = new LinkedList<Object>();
      PictogramElement[] pes = context.getPictogramElements();
      for (PictogramElement pe : pes) {
         Object businessObject = getBusinessObjectForPictogramElement(pe);
         if (businessObject instanceof ISuspendResume) {
            businessObjects.add(businessObject);
         }
      }
      // Execute resume request
      IDebugCommandRequest request = new ExecuteActionRequest(businessObjects.toArray());
      IDebugCommandHandler rc = createCommand();
      rc.execute(request);
   }
   
   /**
    * Instantiates an {@link IDebugCommandHandler} which will do the execution.
    * @return The {@link IDebugCommandHandler} to execute.
    */
   protected abstract IDebugCommandHandler createCommand();
}