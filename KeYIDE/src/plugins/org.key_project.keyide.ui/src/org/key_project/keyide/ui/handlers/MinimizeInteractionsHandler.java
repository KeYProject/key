/**
 * 
 */
package org.key_project.keyide.ui.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.ui.handlers.HandlerUtil;

/**
 * toggles the state for minimizing interactions.
 * 
 * @author Viktor Pfanschilling
 */
public class MinimizeInteractionsHandler extends AbstractHandler {

   /**
    * command id
    */
   public static final String COMMAND_ID = "org.key_project.keyide.ui.commands.minimizeInteractions";

   /** 
    * {@inheritDoc}
    */
   @Override
   public Object execute(ExecutionEvent event) throws ExecutionException {
      HandlerUtil.toggleCommandState(event.getCommand());
      return null;
   }
}
