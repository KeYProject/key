package org.key_project.key4eclipse.resources.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.resources.ui.view.VerificationStatusView;

/**
 * This commands toggles the link with editor/view state.
 * The {@link VerificationStatusView} automatically recognizes the state
 * change and updates the shown content.
 * @author Martin Hentschel
 */
public class LinkWithWorkbenchPartHandler extends AbstractHandler {
   /**
    * {@inheritDoc}
    */
   @Override
   public Object execute(ExecutionEvent event) throws ExecutionException {
      HandlerUtil.toggleCommandState(event.getCommand());
      return null;
   }
}
