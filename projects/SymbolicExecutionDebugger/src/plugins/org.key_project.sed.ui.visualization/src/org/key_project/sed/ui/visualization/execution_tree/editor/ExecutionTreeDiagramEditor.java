package org.key_project.sed.ui.visualization.execution_tree.editor;

import java.io.OutputStream;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.DebugEvent;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.IDebugEventSetListener;
import org.eclipse.debug.core.model.IDebugElement;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.ui.editor.DiagramEditor;
import org.eclipse.swt.widgets.Display;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.serialization.SEDXMLWriter;
import org.key_project.sed.ui.visualization.execution_tree.provider.ExecutionTreeDiagramTypeProvider;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeUtil;
import org.key_project.sed.ui.visualization.execution_tree.wizard.SaveAsExecutionTreeDiagramWizard;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.sed.ui.visualization.util.PaletteHideableDiagramEditor;
import org.key_project.util.java.ArrayUtil;

/**
 * {@link DiagramEditor} for Symbolic Execution Tree Diagrams.
 * @author Martin Hentschel
 */
// TODO: Reload diagram when the domain model file has changed.
// TODO: Synchronize selection with debug view
// TODO: Implement outline view
public class ExecutionTreeDiagramEditor extends PaletteHideableDiagramEditor {
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
   @SuppressWarnings("restriction")
   @Override
   public void doSave(IProgressMonitor monitor) {
      try {
         // Save diagram file
         super.doSave(monitor);
         // Save domain file
         IDiagramTypeProvider diagramTypeProvider = getDiagramTypeProvider();
         if (diagramTypeProvider instanceof ExecutionTreeDiagramTypeProvider) {
            ExecutionTreeDiagramTypeProvider provider = (ExecutionTreeDiagramTypeProvider)diagramTypeProvider;
            // Open output stream to domain file
            OutputStream out = ExecutionTreeUtil.writeDomainFile(diagramTypeProvider.getDiagram());
            // Save domain file
            SEDXMLWriter writer = new SEDXMLWriter();
            writer.write(provider.getDebugTargets(), SEDXMLWriter.DEFAULT_ENCODING, out);
         }
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         throw new RuntimeException(e);
      }
   }

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
         Display.getDefault().asyncExec(new Runnable() {
            @SuppressWarnings("restriction")
            @Override
            public void run() {
               if (getDiagramTypeProvider().isAutoUpdateAtRuntime()) {
                  PictogramElement[] oldSelection = getSelectedPictogramElements();
                  PictogramElement[] elements = GraphitiUtil.getAllPictogramElements(getDiagram());
                  getDiagramTypeProvider().getNotificationService().updatePictogramElements(elements);
                  try {
                     selectPictogramElements(oldSelection);
                  }
                  catch (Exception e) {
                     // Can go wrong, nothing to do.
                  }
               }
               else {
                  refreshContent();
               }
            }
         });
      }
   }
   
   /**
    * Returns the shown {@link Diagram}.
    * @return The shown {@link Diagram}.
    */
   protected Diagram getDiagram() {
      IDiagramTypeProvider typeProvider = getDiagramTypeProvider();
      return typeProvider != null ? typeProvider.getDiagram() : null;
   }
}
