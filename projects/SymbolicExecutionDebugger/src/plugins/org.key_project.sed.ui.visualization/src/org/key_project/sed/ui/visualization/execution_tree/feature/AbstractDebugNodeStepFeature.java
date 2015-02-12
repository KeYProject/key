/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
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
import org.eclipse.debug.core.model.IStep;
import org.eclipse.debug.internal.ui.commands.actions.ExecuteActionRequest;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.ICustomContext;
import org.eclipse.graphiti.features.custom.AbstractCustomFeature;
import org.eclipse.graphiti.features.custom.ICustomFeature;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;

/**
 * An {@link ICustomFeature} which provides the basic functionality to
 * work with {@link IStep} business objects.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public abstract class AbstractDebugNodeStepFeature extends AbstractCustomFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} to use.
    */
   public AbstractDebugNodeStepFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canExecute(ICustomContext context) {
      boolean canExecute = true;
      PictogramElement[] pes = context.getPictogramElements();
      List<IStep> stepsToHandle = new LinkedList<IStep>();
      if (pes != null) {
         int i = 0;
         while (i < pes.length && canExecute) {
            Object businessObject = getBusinessObjectForPictogramElement(pes[i]);
            if (businessObject instanceof IStep) {
               IStep step = (IStep)businessObject;
               stepsToHandle.add(step);
               canExecute = canExecute(step);
            }
            i++;
         }
      }
      return canExecute && checkCompatibility(stepsToHandle);
   }
   
   /**
    * Checks if the found {@link IStep}s are compatible.
    * @param stepsToHandle The {@link IStep}s to check.
    * @return {@code true} {@link IStep}s are compatible, {@code false} {@link IStep}s are incompatible.
    */
   protected boolean checkCompatibility(List<IStep> stepsToHandle) {
      return stepsToHandle.size() == 1; // Only exactly one IStep is executable at the same time
   }

   /**
    * Checks if the execution on the given {@link IStep} is allowed.
    * @param step The {@link IStep} to check.
    * @return {@code true} can execute, {@code false} can not execute.
    */
   protected abstract boolean canExecute(IStep step);

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
         if (businessObject instanceof IStep) {
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