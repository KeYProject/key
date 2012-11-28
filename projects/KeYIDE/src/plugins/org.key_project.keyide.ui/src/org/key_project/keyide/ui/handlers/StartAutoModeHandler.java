package org.key_project.keyide.ui.handlers;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.keyide.ui.editor.IProofEnvironmentProvider;
import org.key_project.keyide.ui.job.AbstractKeYEnvironmentJob;

public class StartAutoModeHandler extends AbstractSaveExecutionHandler {

   @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
      IEditorPart editorPart = HandlerUtil.getActiveEditor(event);
      final IProofEnvironmentProvider proofProvider = (IProofEnvironmentProvider)editorPart.getAdapter(IProofEnvironmentProvider.class);
      if (proofProvider != null && 
          proofProvider.getKeYEnvironment().getUi().isAutoModeSupported(proofProvider.getProof()) && 
          !proofProvider.getKeYEnvironment().getMediator().autoMode()) {
         new AbstractKeYEnvironmentJob("Auto Mode", proofProvider.getKeYEnvironment()) {
            @Override
            protected IStatus run(IProgressMonitor monitor) {
               monitor.beginTask("Proving with KeY", IProgressMonitor.UNKNOWN);
               proofProvider.getKeYEnvironment().getUi().startAndWaitForAutoMode(proofProvider.getProof());
               monitor.done();
               return Status.OK_STATUS;
            }
            }.schedule();
      }
      return null;
   }

}

