package org.key_project.sed.key.ui.command;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jface.window.Window;
import org.key_project.sed.key.core.model.breakpoints.WatchPoint;
import org.key_project.sed.key.ui.dialogs.AddKeYWatchpointDialog;
import org.key_project.util.eclipse.WorkbenchUtil;

public class AddWatchpointHandler extends AbstractHandler {

   @Override
   public Object execute(ExecutionEvent event) throws ExecutionException {
      AddKeYWatchpointDialog watchpointDialog = new AddKeYWatchpointDialog(WorkbenchUtil.getActiveShell());
      watchpointDialog.create();
      if (watchpointDialog.open() == Window.OK) {
         WatchPoint watchpoint = new WatchPoint();
         watchpoint.setCondition(watchpointDialog.getCondition());
       } 
      
      return null;
   }

}
