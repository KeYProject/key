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

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.IRemoveFeature;
import org.eclipse.graphiti.features.context.ICustomContext;
import org.eclipse.graphiti.features.context.IRemoveContext;
import org.eclipse.graphiti.features.context.impl.RemoveContext;
import org.eclipse.graphiti.features.context.impl.UpdateContext;
import org.eclipse.graphiti.features.custom.AbstractCustomFeature;
import org.eclipse.graphiti.features.custom.ICustomFeature;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.platform.IDiagramEditor;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.ui.visualization.execution_tree.provider.ExecutionTreeFeatureProvider;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.util.java.CollectionUtil;

/**
 * An {@link ICustomFeature} that connects the given {@link Diagram}
 * with specified {@link ISEDDebugTarget}s. The {@link ISEDDebugTarget}
 * are specified via property {@link #PROPERTY_DEBUG_TARGETS} of the given
 * {@link ICustomContext}.
 * @author Martin Hentschel
 */
public class DebugTargetConnectFeature extends AbstractCustomFeature {
   /**
    * Property for an {@link ISEDDebugTarget} array which contains
    * the {@link ISEDDebugTarget} to link with {@link #getDiagram()}.
    */
   public static final String PROPERTY_DEBUG_TARGETS = "debugTargets";

   /**
    * Property for an {@link Object} array which contains
    * the {@link Object}s to select after reconstructing {@link #getDiagram()}.
    */
   public static final Object PROPERTY_ELEMENTS_TO_SELECT = "elementsToSelect";
   
   /**
    * Property for an {@link IProgressHandler} instance which is used
    * to detect when the feature execution has started and is stopped.
    */
   public static final Object PROPERTY_PROGRESS_HANDLER = "progressHandler";

   /**
    * Indicates that changes were made in {@link #execute(ICustomContext)} or not.
    */
   private boolean changesDone = false;
   
   /**
    * Constructor.
    * @param fp The {@link ExecutionTreeFeatureProvider} which provides this {@link ICustomFeature}.
    */
   public DebugTargetConnectFeature(ExecutionTreeFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ExecutionTreeFeatureProvider getFeatureProvider() {
      return (ExecutionTreeFeatureProvider)super.getFeatureProvider();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getDescription() {
      return "Creates a connection between this diagram and the specified debug targets.";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return "Connect diagram with debug targets";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canExecute(ICustomContext context) {
      Object obj = context.getProperty(PROPERTY_DEBUG_TARGETS);
      return obj instanceof ISEDDebugTarget[];
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void execute(ICustomContext context) {
      // Get progress handler
      Object contextHandler = context.getProperty(PROPERTY_PROGRESS_HANDLER);
      IProgressHandler handler = null;
      if (contextHandler instanceof IProgressHandler) {
         handler = (IProgressHandler)contextHandler;
         handler.executionStarted(this);
      }
      try {
         // Define monitor to use
         IProgressMonitor monitor = GraphitiUtil.getProgressMonitor(context);
         // Change connection
         Object obj = context.getProperty(PROPERTY_DEBUG_TARGETS);
         if (obj instanceof ISEDDebugTarget[]) {
            // Clear diagram
            monitor.beginTask("Change diagram content", 3);
            Object[] oldLinkedObjects = getAllBusinessObjectsForPictogramElement(getDiagram());
            for (Object oldObj : oldLinkedObjects) {
               if (!monitor.isCanceled() && oldObj instanceof ISEDDebugTarget) {
                  ISEDThread[] threads = ((ISEDDebugTarget)oldObj).getSymbolicThreads();
                  for (ISEDThread thread : threads) {
                     if (!monitor.isCanceled()) {
                        PictogramElement[] elements = getFeatureProvider().getAllPictogramElementsForBusinessObject(thread);
                        for (PictogramElement pictogramElement : elements) {
                           if (!monitor.isCanceled()) {
                              IRemoveContext removeContext = new RemoveContext(pictogramElement);
                              IRemoveFeature feature = getFeatureProvider().getRemoveFeatureIgnoreReadonlyState(removeContext);
                              Assert.isNotNull(feature, "No remove feature available for \"" + removeContext + "\".");
                              feature.execute(removeContext);
                           }
                        }
                     }
                  }
               }
            }
            monitor.worked(1);
            // Recreate diagram with new content
            if (!monitor.isCanceled()) {
               link(getDiagram(), (ISEDDebugTarget[])obj);
            }
            // Update diagram
            if (!monitor.isCanceled()) {
               UpdateContext updateContext = new UpdateContext(getDiagram());
               updateContext.putProperty(GraphitiUtil.CONTEXT_PROPERTY_MONITOR, new SubProgressMonitor(monitor, 1));
               getFeatureProvider().updateIfPossible(updateContext);
            }
            changesDone = true;
            monitor.worked(1);
            // Select elements
            Object toSelect = context.getProperty(PROPERTY_ELEMENTS_TO_SELECT);
            if (toSelect instanceof Object[]) {
               IDiagramEditor editor = getFeatureProvider().getDiagramTypeProvider().getDiagramEditor();
               if (editor != null) {
                  List<PictogramElement> pes = new LinkedList<PictogramElement>();
                  for (Object businessObject : (Object[])toSelect) {
                     PictogramElement[] boPes = getFeatureProvider().getAllPictogramElementsForBusinessObject(businessObject);
                     CollectionUtil.addAll(pes, boPes);
                  }
                  editor.setPictogramElementsForSelection(pes.toArray(new PictogramElement[pes.size()]));
               }
            }
            monitor.worked(1);
            monitor.done();
         }
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
         throw new RuntimeException(e);
      }
      finally {
         if (handler != null) {
            handler.executionFinished(this);
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasDoneChanges() {
      return changesDone;
   }
   
   /**
    * Instances of this class are used to observe the execution progress.
    * @author Martin Hentschel
    */
   public static interface IProgressHandler {
      /**
       * When the execution has started.
       * @param feature The {@link DebugTargetConnectFeature}.
       */
      public void executionStarted(DebugTargetConnectFeature feature);
      
      /**
       * When the execution has finished.
       * @param feature The {@link DebugTargetConnectFeature}.
       */
      public void executionFinished(DebugTargetConnectFeature feature);
   }
}