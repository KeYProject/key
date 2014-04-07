package org.key_project.keyide.ui.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.ui.handlers.HandlerUtil;

/**
 * Toggles the stop at breakpoints state.
 * @author Martin Hentschel
 */
public class BreakpointToggleHandler extends AbstractHandler {
   /**
    * The command ID.
    */
   public static final String COMMAND_ID = "org.key_project.keyide.ui.commands.stopAtBreakpointsCommand";
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Object execute(ExecutionEvent event) throws ExecutionException {
      HandlerUtil.toggleCommandState(event.getCommand());
      return null;
   }
}
