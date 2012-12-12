package org.key_project.keyide.ui.handlers;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.services.IEvaluationService;
import org.key_project.key4eclipse.common.ui.handler.AbstractSaveExecutionHandler;
import org.key_project.keyide.ui.editor.IProofEnvironmentProvider;
import org.key_project.keyide.ui.job.AbstractKeYEnvironmentJob;
import org.key_project.keyide.ui.util.KeYToUIUtil;

public class StartAutoModeHandler extends AbstractSaveExecutionHandler {   
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
      //initialize values for execution
      IEditorPart editorPart = HandlerUtil.getActiveEditor(event);
      final IEvaluationService evaluationService = (IEvaluationService)PlatformUI.getWorkbench().getActiveWorkbenchWindow().getService(IEvaluationService.class);
      final IProofEnvironmentProvider proofProvider = (IProofEnvironmentProvider)editorPart.getAdapter(IProofEnvironmentProvider.class);
      if (proofProvider != null && 
          proofProvider.getKeYEnvironment().getUi().isAutoModeSupported(proofProvider.getProof()) && 
          !proofProvider.getKeYEnvironment().getMediator().autoMode()) {
         //refresh GUI properly
         proofProvider.getKeYEnvironment().getMediator().setMaxAutomaticSteps(2);
         proofProvider.getKeYEnvironment().getUi().notifyAutoModeBeingStarted();
         KeYToUIUtil.refreshUI(evaluationService);
         new AbstractKeYEnvironmentJob("Auto Mode", proofProvider.getKeYEnvironment()) {
            // job that starts the automode in KeY
            @Override
            protected IStatus run(IProgressMonitor monitor) {
               monitor.beginTask("Proving with KeY", IProgressMonitor.UNKNOWN);
               proofProvider.getKeYEnvironment().getMediator().setMaxAutomaticSteps(Integer.MAX_VALUE);
               proofProvider.getKeYEnvironment().getUi().startAndWaitForAutoMode(proofProvider.getProof());
               //refresh GUI properly
               proofProvider.getKeYEnvironment().getUi().notifyAutomodeStopped();
               KeYToUIUtil.refreshUI(evaluationService);
               
               monitor.done();
               return Status.OK_STATUS;
            }
         }.schedule();
      }
      return null;
   }
}

