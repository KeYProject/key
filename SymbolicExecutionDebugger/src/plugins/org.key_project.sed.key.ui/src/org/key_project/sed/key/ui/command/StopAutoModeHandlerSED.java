package org.key_project.sed.key.ui.command;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.common.ui.handler.AbstractSaveExecutionHandler;
import org.key_project.keyide.ui.handlers.StopAutoModeHandler;
import org.key_project.sed.key.ui.view.ProofView;

/**
 * Class to handle stop auto mode command on {@link ProofView}.
 * @author Seena Vellaramkalayil
 */
public class StopAutoModeHandlerSED extends AbstractSaveExecutionHandler {
   /**
    * {@inheritDoc}
    */
   @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
      IWorkbenchPart part = HandlerUtil.getActivePart(event);
      StopAutoModeHandler.stopAutoMode(part);
      return null;
   }
}
