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

package org.key_project.sed.ui.visualization.execution_tree.editor;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Status;
import org.eclipse.debug.core.DebugEvent;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.IDebugEventSetListener;
import org.eclipse.debug.core.model.IDebugElement;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.gef.ContextMenuProvider;
import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.notification.INotificationService;
import org.eclipse.graphiti.ui.editor.DiagramEditor;
import org.eclipse.swt.widgets.Display;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.ui.visualization.execution_tree.service.SEDNotificationService;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeUtil;
import org.key_project.sed.ui.visualization.execution_tree.wizard.SaveAsExecutionTreeDiagramWizard;
import org.key_project.sed.ui.visualization.util.CustomizableDiagramEditorContextMenuProvider;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.sed.ui.visualization.util.PaletteHideableDiagramEditor;
import org.key_project.util.eclipse.job.AbstractWorkbenchPartJob;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.ArrayUtil;

/**
 * {@link DiagramEditor} for Symbolic Execution Tree Diagrams.
 * @author Martin Hentschel
 */
// TODO: Reload diagram when the domain model file has changed.
public class ExecutionTreeDiagramEditor extends PaletteHideableDiagramEditor {
   /**
    * Indicates that this editor is read-onl or editable otherwise.
    */
   private boolean readOnly;

   /**
    * Listens for debug events.
    */
   private IDebugEventSetListener debugListener = new IDebugEventSetListener() {
      @Override
      public void handleDebugEvents(DebugEvent[] events) {
         ExecutionTreeDiagramEditor.this.handleDebugEvents(events);
      }
   };

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isSaveAsAllowed() {
      return true;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void doSaveAs() {
      SaveAsExecutionTreeDiagramWizard.openWizard(getSite().getShell(), getDiagramTypeProvider());
   }

   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("restriction")
   @Override
   protected void registerBOListener() {
      super.registerBOListener();
      DebugPlugin.getDefault().addDebugEventListener(debugListener);
   }

   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("restriction")
   @Override
   protected void unregisterBOListener() {
      super.unregisterBOListener();
      DebugPlugin.getDefault().removeDebugEventListener(debugListener);
   }

   /**
    * Handles the detected debug events. 
    * @param events The detected debug events.
    */
   protected void handleDebugEvents(DebugEvent[] events) {
      // Check if an update of the diagram is required.
      ISEDDebugTarget[] targets = ExecutionTreeUtil.getAllDebugTargets(getDiagramTypeProvider());
      boolean updateRequired = false;
      int i = 0;
      while (!updateRequired && i < events.length) {
         if (DebugEvent.SUSPEND == events[i].getDetail() ||
             DebugEvent.SUSPEND == events[i].getDetail()) {
            if (events[i].getSource() instanceof IDebugElement) {
               IDebugTarget target = ((IDebugElement)events[i].getSource()).getDebugTarget();
               if (target instanceof ISEDDebugTarget) {
                  updateRequired = ArrayUtil.contains(targets, target);
               }
            }
         }
         i++;
      }
      // Update diagram content if required.
      if (updateRequired) {
         // Do an asynchronous update in the UI thread (same behavior as DomainModelChangeListener which is responsible for changes in EMF objects)
         AbstractWorkbenchPartJob.cancelJobs(this);
         new AbstractWorkbenchPartJob("Updating Symbolic Execution Tree", this) {
            @Override
            protected IStatus run(IProgressMonitor monitor) {
               return updateDiagramInJob(monitor);
            }
         }.schedule();
      }
   }
   
   /**
    * Changes the content of the shown {@link Diagram}.
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The result {@link IStatus}.
    */
   protected IStatus updateDiagramInJob(IProgressMonitor monitor) {
      try {
         SWTUtil.checkCanceled(monitor);
         if (getDiagramTypeProvider().isAutoUpdateAtRuntime()) {
            PictogramElement[] oldSelection = getSelectedPictogramElements();
            PictogramElement[] elements = GraphitiUtil.getAllPictogramElements(getDiagram());
            INotificationService notificationService = getDiagramTypeProvider().getNotificationService();
            if (notificationService instanceof SEDNotificationService) {
               ((SEDNotificationService)notificationService).updatePictogramElements(elements, monitor);
            }
            else {
               notificationService.updatePictogramElements(elements);
            }
            selectPictogramElementsThreadSave(oldSelection);
         }
         else {
            refreshContent();
         }
         return Status.OK_STATUS;
      }
      catch (OperationCanceledException e) {
         return Status.CANCEL_STATUS;
      }
      catch (Exception e) {
         return LogUtil.getLogger().createErrorStatus(e);
      }
   }
   
   /**
    * Thread and exception save execution of {@link #selectPictogramElements(PictogramElement[])}.
    * @param pictogramElements The {@link PictogramElement}s to select.
    */
   protected void selectPictogramElementsThreadSave(final PictogramElement[] pictogramElements) {
      Display.getDefault().syncExec(new Runnable() {
         @Override
         public void run() {
            try {
               selectPictogramElements(pictogramElements);
            }
            catch (Exception e) {
               // Can go wrong, nothing to do.
            }
         }
      });
   }

   /**
    * Returns the shown {@link Diagram}.
    * @return The shown {@link Diagram}.
    */
   protected Diagram getDiagram() {
      IDiagramTypeProvider typeProvider = getDiagramTypeProvider();
      return typeProvider != null ? typeProvider.getDiagram() : null;
   }
   
   /**
    * Checks if this editor is read-only or editable.
    * @return {@code true} read-only, {@code false} editable
    */
   public boolean isReadOnly() {
      return readOnly;
   }

   /**
    * Defines if this editor is read-only or editable.
    * @param readOnly {@code true} read-only, {@code false} editable
    */
   public void setReadOnly(boolean readOnly) {
      this.readOnly = readOnly;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isDirty() {
      return !isReadOnly() && super.isDirty();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected ContextMenuProvider createContextMenuProvider() {
      return new CustomizableDiagramEditorContextMenuProvider(getGraphicalViewer(), 
                                                              getActionRegistry(), 
                                                              getConfigurationProvider(),
                                                              !isReadOnly(),
                                                              !isReadOnly());
   }
}