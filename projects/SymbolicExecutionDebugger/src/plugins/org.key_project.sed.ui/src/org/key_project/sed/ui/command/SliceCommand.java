package org.key_project.sed.ui.command;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.debug.core.DebugException;
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
      try {
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
                        ((ISEDSlicer) dialog.getFirstResult()).slice(seedNode, seedVariable);
                     }
                  }
               }
            }
         }
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(HandlerUtil.getActiveShell(event), e);
      }
      return null;
   }
}
