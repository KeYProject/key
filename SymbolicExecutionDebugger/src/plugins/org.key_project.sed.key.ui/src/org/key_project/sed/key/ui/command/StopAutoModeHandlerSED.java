package org.key_project.sed.key.ui.command;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.ui.IViewPart;
import org.key_project.key4eclipse.common.ui.handler.AbstractSaveExecutionHandler;
import org.key_project.sed.key.ui.view.ManualView;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * Class to handle stop auto mode command on {@link ManualView}.
 * @author Seena Vellaramkalayil
 *
 */
public class StopAutoModeHandlerSED extends AbstractSaveExecutionHandler {

   /**
    * {@inheritDoc}
    */
   @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
      //make sure Manual Rule Application View is opened
      if (WorkbenchUtil.findView(ManualView.VIEW_ID) != null) {
         IViewPart viewPart = WorkbenchUtil.openView(ManualView.VIEW_ID);
         if (viewPart instanceof ManualView) {
            ManualView manualView = (ManualView) viewPart;
            if (manualView != null && manualView.getProof() != null 
                && manualView.getEnvironment().getProofControl().isInAutoMode()) {
               manualView.getEnvironment().getProofControl().stopAutoMode();
            }
         }
      }
      return null;
   }

}
