package org.key_project.keyide.ui.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.ui.handlers.HandlerUtil;


/**
 * toggles the state for showing symbolic execution tree only
 * 
 * @author Seena Vellaramkalayil, Leonard Goetz
 *
 */
public class ShowSymbolicExecutionTreeOnlyHandler extends AbstractHandler{
   
   /**
    * the command id
    */
   public static final String COMMAND_ID = "org.key_project.keyide.ui.commands.showSymbolicExecutionTreeOnly";

   /**
    * {@inheritDoc}
    */
   @Override
   public Object execute(ExecutionEvent event) throws ExecutionException {
      HandlerUtil.toggleCommandState(event.getCommand());
      return null;
   }

}
