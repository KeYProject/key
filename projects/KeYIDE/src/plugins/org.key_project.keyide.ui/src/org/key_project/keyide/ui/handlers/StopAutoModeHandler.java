package org.key_project.keyide.ui.handlers;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.common.ui.handler.AbstractSaveExecutionHandler;
import org.key_project.keyide.ui.editor.IProofEnvironmentProvider;

public class StopAutoModeHandler extends AbstractSaveExecutionHandler {
   /**
    * {@inheritDoc}
    */
   @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
      //initialize values
      IEditorPart editorPart = HandlerUtil.getActiveEditor(event);
      IProofEnvironmentProvider proofProvider = (IProofEnvironmentProvider)editorPart.getAdapter(IProofEnvironmentProvider.class);
      if (proofProvider != null && proofProvider.getKeYEnvironment().getMediator().autoMode()) {
         proofProvider.getKeYEnvironment().getUi().stopAutoMode();
      }
      return null;
   }

}
