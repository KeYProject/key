package de.hentschel.visualdbc.dbcmodel.diagram.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.ui.handlers.HandlerUtil;

/**
 * <p>
 * Handler which is executed to enable or disable the highlighting.
 * </p>
 * <p>
 * During execution only the command state is changed. The diagram editors
 * itself registers the change and updates the shown content.
 * </p>
 * @author Martin Hentschel
 * @generated NOT
 */
public class AutomaticProofReferenceHighlightHandler extends AbstractHandler {
   /**
    * {@inheritDoc}
    */
   @Override
   public Object execute(ExecutionEvent event) throws ExecutionException {
      HandlerUtil.toggleCommandState(event.getCommand());
      return null; 
   }
}
