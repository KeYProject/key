package org.key_project.sed.key.ui.command;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.ui.IViewPart;
import org.key_project.key4eclipse.common.ui.handler.AbstractSaveExecutionHandler;
import org.key_project.sed.key.ui.view.ProofView;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * Class to handle stop auto mode command on {@link ProofView}.
 * @author Seena Vellaramkalayil
 *
 */
public class StopAutoModeHandlerSED extends AbstractSaveExecutionHandler {

   /**
    * {@inheritDoc}
    */
   @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
      //make sure Proof View is opened
      if (WorkbenchUtil.findView(ProofView.VIEW_ID) != null) {
         IViewPart viewPart = WorkbenchUtil.openView(ProofView.VIEW_ID);
         if (viewPart instanceof ProofView) {
            ProofView proofView = (ProofView) viewPart;
            if (proofView != null && proofView.getProof() != null 
                && proofView.getEnvironment().getProofControl().isInAutoMode()) {
               proofView.getEnvironment().getProofControl().stopAutoMode();
            }
         }
      }
      return null;
   }

}
