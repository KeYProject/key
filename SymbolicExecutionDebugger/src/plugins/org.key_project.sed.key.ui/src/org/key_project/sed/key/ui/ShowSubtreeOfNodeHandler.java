package org.key_project.sed.key.ui;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.common.ui.handler.AbstractSaveExecutionHandler;

public class ShowSubtreeOfNodeHandler extends AbstractSaveExecutionHandler {

   public static final String COMMAND_ID = "org.key_project.sed.key.ui.showSubtreeCommand";
   
         @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
      HandlerUtil.toggleCommandState(event.getCommand());
      return null;
   }

}
