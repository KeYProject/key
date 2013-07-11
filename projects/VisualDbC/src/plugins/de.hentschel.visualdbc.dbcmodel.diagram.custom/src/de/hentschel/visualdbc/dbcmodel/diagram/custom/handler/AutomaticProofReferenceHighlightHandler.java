package de.hentschel.visualdbc.dbcmodel.diagram.custom.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.ui.handlers.HandlerUtil;

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
