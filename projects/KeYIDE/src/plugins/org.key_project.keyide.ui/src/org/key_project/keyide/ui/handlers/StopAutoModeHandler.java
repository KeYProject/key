package org.key_project.keyide.ui.handlers;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.services.IEvaluationService;
import org.key_project.keyide.ui.editor.IProofEnvironmentProvider;
import org.key_project.keyide.ui.tester.AutoModeTester;

public class StopAutoModeHandler extends AbstractSaveExecutionHandler {


   
   /**
    * {@inheritDoc}
    */
   @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
      //initialize values
      IEditorPart editorPart = HandlerUtil.getActiveEditor(event);
      IProofEnvironmentProvider proofProvider = (IProofEnvironmentProvider)editorPart.getAdapter(IProofEnvironmentProvider.class);
      IWorkbenchWindow window = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
      IEvaluationService evaluationService = (IEvaluationService) window.getService(IEvaluationService.class);

      if (proofProvider != null && proofProvider.getKeYEnvironment().getMediator().autoMode()) {
         //refresh GUI properly
         proofProvider.getKeYEnvironment().getUi().notifyAutomodeStopped();
         if (evaluationService != null) {
            evaluationService.requestEvaluation(AutoModeTester.PROPERTY_NAMESPACE + "." + AutoModeTester.PROPERTY_START);
            evaluationService.requestEvaluation(AutoModeTester.PROPERTY_NAMESPACE + "." + AutoModeTester.PROPERTY_STOP);
         }
         proofProvider.getKeYEnvironment().getUi().stopAutoMode();
      }
      return null;
   }

}
