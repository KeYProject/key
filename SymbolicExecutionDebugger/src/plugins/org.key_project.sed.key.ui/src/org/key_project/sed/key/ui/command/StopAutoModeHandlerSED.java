package org.key_project.sed.key.ui.command;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.ui.IViewPart;
import org.key_project.key4eclipse.common.ui.handler.AbstractSaveExecutionHandler;
import org.key_project.sed.key.ui.view.ManualView;
import org.key_project.util.eclipse.WorkbenchUtil;

public class StopAutoModeHandlerSED extends AbstractSaveExecutionHandler {

   @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
      if (WorkbenchUtil.findView(ManualView.VIEW_ID) != null) {
         IViewPart viewPart = WorkbenchUtil.openView(ManualView.VIEW_ID);
         if (viewPart instanceof ManualView) {
            ManualView manualView = (ManualView) viewPart;
            if (manualView != null && manualView.getProof() != null && manualView.getEnvironment().getProofControl().isInAutoMode()) {
               manualView.getEnvironment().getProofControl().stopAutoMode();
            }
         }
      }
      return null;
   }

}
