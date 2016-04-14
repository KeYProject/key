package org.key_project.sed.key.ui.command;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.common.ui.handler.AbstractSaveExecutionHandler;
import org.key_project.keyide.ui.handlers.StartAutoModeHandler;
import org.key_project.sed.key.ui.view.ProofView;

/**
 * Class to handle the start auto mode command in the {@link ProofView}.
 * @author Seena Vellaramkalayil
 */
public class StartAutoModeHandlerSED extends AbstractSaveExecutionHandler {
   /**
    * {@inheritDoc}
    */
   @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
      IWorkbenchPart part = HandlerUtil.getActivePart(event);
      StartAutoModeHandler.startAutoMode(part);
      return null;
   }   
}