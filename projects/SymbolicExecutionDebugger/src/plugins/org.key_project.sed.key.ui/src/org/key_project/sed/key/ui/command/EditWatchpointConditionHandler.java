package org.key_project.sed.key.ui.command;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.window.Window;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.sed.key.core.model.breakpoints.WatchPoint;
import org.key_project.sed.key.ui.dialogs.AddKeYWatchpointDialog;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.eclipse.swt.SWTUtil;

public class EditWatchpointConditionHandler extends AbstractHandler {

   @Override
   public Object execute(ExecutionEvent event) throws ExecutionException {
      
      ISelection selection = HandlerUtil.getCurrentSelection(event);
      Object[] elements = SWTUtil.toArray(selection);
      WatchPoint watchpoint = null;
      for (Object element : elements) {
         // Find proof
         if (element instanceof WatchPoint) {
            watchpoint = ((WatchPoint)element);
         }
      }  
      if(watchpoint != null){
         AddKeYWatchpointDialog watchpointDialog = new AddKeYWatchpointDialog(WorkbenchUtil.getActiveShell());
         watchpointDialog.create();
         if (watchpointDialog.open() == Window.OK) {
            watchpoint.setCondition(watchpointDialog.getCondition());
          }  
      }     
      return null;
   }

}
