package org.key_project.sed.key.ui.command;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.ui.IViewPart;
import org.key_project.key4eclipse.common.ui.handler.AbstractSaveExecutionHandler;
import org.key_project.keyide.ui.job.AbstractKeYEnvironmentJob;
import org.key_project.sed.key.ui.view.ProofView;
import org.key_project.util.eclipse.WorkbenchUtil;

import de.uka.ilkd.key.proof.Proof;

/**
 * Class to handle the start auto mode command in the {@link ProofView}.
 * @author Seena Vellaramkalayil
 *
 */
public class StartAutoModeHandlerSED extends AbstractSaveExecutionHandler {

   @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
    //initialize values for execution
    if (WorkbenchUtil.findView(ProofView.VIEW_ID) != null) {
       IViewPart viewPart = WorkbenchUtil.openView(ProofView.VIEW_ID);
       if (viewPart instanceof ProofView) {
         final ProofView proofView = (ProofView) viewPart;
         if (proofView.getProof() != null) {
            if (!proofView.getEnvironment().getProofControl().isInAutoMode()
                && proofView.getProof() != null) {
               new AbstractKeYEnvironmentJob("Auto Mode", proofView.getEnvironment()) {
                  // job that starts the automode in KeY
                  @Override
                  protected IStatus run(IProgressMonitor monitor) {
                     monitor.beginTask("Proving with KeY", IProgressMonitor.UNKNOWN);
                     Proof proof = proofView.getProof();
                     proof.getActiveStrategy(); // Make sure that the strategy is initialized correctly
                     proofView.getEnvironment().getProofControl().startAndWaitForAutoMode(proof);
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
   
   


