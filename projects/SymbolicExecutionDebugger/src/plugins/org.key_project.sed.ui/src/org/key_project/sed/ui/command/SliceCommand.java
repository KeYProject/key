package org.key_project.sed.ui.command;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.debug.core.model.IVariable;
import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDVariable;
import org.key_project.sed.core.slicing.ISEDSlicer;
import org.key_project.sed.core.util.LogUtil;
import org.key_project.sed.ui.provider.SEDSlicerLabelProvider;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.eclipse.swt.dialog.ElementListSelectionDialog;
import org.key_project.util.java.ArrayUtil;

/**
 * Opens a dialog to select an available {@link ISEDSlicer} and performs the slicing.
 * @author Martin Hentschel
 */
public class SliceCommand extends AbstractHandler {
   /**
    * {@inheritDoc}
    */
   @Override
   public Object execute(ExecutionEvent event) throws ExecutionException {
      ISelection selection = HandlerUtil.getCurrentSelection(event);
      Object[] elements = SWTUtil.toArray(selection);
      for (Object element : elements) {
         if (element instanceof ISEDVariable) {
            ISEDVariable seedVariable = (ISEDVariable) element;
            ISEDDebugTarget target = seedVariable.getDebugTarget();
            if (target != null && seedVariable.getStackFrame() instanceof ISEDDebugNode) {
               ISEDDebugNode seedNode = (ISEDDebugNode) seedVariable.getStackFrame();
               ISEDSlicer[] slicer = target.getSlicer(seedNode, seedVariable);
               if (!ArrayUtil.isEmpty(slicer)) {
                  ElementListSelectionDialog dialog = new ElementListSelectionDialog(HandlerUtil.getActiveShell(event), 
                                                                                     ArrayContentProvider.getInstance(), 
                                                                                     new SEDSlicerLabelProvider());
                  dialog.setAllowMultiple(false);
                  dialog.setHelpAvailable(false);
                  dialog.setInitialSelections(new ISEDSlicer[] {slicer[0]});
                  dialog.setTitle("Slice Symbolic Execution Tree");
                  dialog.setMessage("Select the slicing algorithm to use.");
                  dialog.setInput(slicer);
                  dialog.open();
                  if (dialog.getFirstResult() instanceof ISEDSlicer) {
                     SliceJob job = new SliceJob(seedNode, seedVariable, (ISEDSlicer) dialog.getFirstResult());
                     job.schedule();
                  }
               }
            }
         }
      }
      return null;
   }
   
   /**
    * A {@link Job} in which an {@link ISEDSlicer} is performed.
    * @author Martin Hentschel
    */
   public static class SliceJob extends Job {
      /**
       * The seed {@link ISEDDebugNode}.
       */
      private final ISEDDebugNode seedNode;
      
      /**
       * The seed {@link IVariable}. 
       */
      private final ISEDVariable seedVariable;
      
      /**
       * The {@link ISEDSlicer} to perform.
       */
      private final ISEDSlicer slicer;
      
      /**
       * Constructor.
       * @param seedNode The seed {@link ISEDDebugNode}.
       * @param seedVariable The seed {@link IVariable}.
       * @param slicer The {@link ISEDSlicer} to perform.
       */
      public SliceJob(ISEDDebugNode seedNode, ISEDVariable seedVariable, ISEDSlicer slicer) {
         super("Slicing Symbolic Execution Tree");
         this.seedNode = seedNode;
         this.seedVariable = seedVariable;
         this.slicer = slicer;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      protected IStatus run(IProgressMonitor monitor) {
         try {
            slicer.slice(seedNode, seedVariable, monitor);
            return Status.OK_STATUS;
         }
         catch (OperationCanceledException e) {
            return Status.CANCEL_STATUS;
         }
         catch (Exception e) {
            return LogUtil.getLogger().createErrorStatus(e);
         }
      }
   }
}
