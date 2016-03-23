package org.key_project.sed.key.ui.command;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.ui.IViewPart;
import org.key_project.key4eclipse.common.ui.handler.AbstractSaveExecutionHandler;
import org.key_project.keyide.ui.job.AbstractKeYEnvironmentJob;
import org.key_project.sed.key.ui.view.ManualView;
import org.key_project.util.eclipse.WorkbenchUtil;

import de.uka.ilkd.key.proof.Proof;

public class StartAutoModeHandlerSED extends AbstractSaveExecutionHandler{

   @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
      // TODO Auto-generated method stub
    //initialize values for execution
    if (WorkbenchUtil.findView(ManualView.VIEW_ID) != null) {
       IViewPart viewPart = WorkbenchUtil.openView(ManualView.VIEW_ID);
       if (viewPart instanceof ManualView) {
         final ManualView manualView = (ManualView)viewPart;
         if (manualView.getProof() != null) {
            if (!manualView.getEnvironment().getProofControl().isInAutoMode() &&
                manualView.getProof() != null) {
               new AbstractKeYEnvironmentJob("Auto Mode", manualView.getEnvironment()) {
                  // job that starts the automode in KeY
                  @Override
                  protected IStatus run(IProgressMonitor monitor) {
                     monitor.beginTask("Proving with KeY", IProgressMonitor.UNKNOWN);
                     Proof proof = manualView.getProof();
                     proof.getActiveStrategy(); // Make sure that the strategy is initialized correctly, otherwise the used settings are different to the one defined by the strategysettings which are shown in the UI.
                     manualView.getEnvironment().getProofControl().startAndWaitForAutoMode(proof);
                     monitor.done();
                     return Status.OK_STATUS;
                  }
               }.schedule();
            }
      }
    }
   }
    return null;
   }
   
}
   
   


