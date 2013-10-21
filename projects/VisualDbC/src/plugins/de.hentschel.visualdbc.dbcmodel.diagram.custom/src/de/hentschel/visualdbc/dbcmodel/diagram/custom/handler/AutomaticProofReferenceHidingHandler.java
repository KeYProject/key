package de.hentschel.visualdbc.dbcmodel.diagram.custom.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.handlers.RadioState;

public class AutomaticProofReferenceHidingHandler extends AbstractHandler {
   /**
    * {@inheritDoc}
    */
   @Override
   public Object execute(ExecutionEvent event) throws ExecutionException {
      if (!HandlerUtil.matchesRadioState(event)) {
         String currentState = event.getParameter(RadioState.PARAMETER_ID);      
         HandlerUtil.updateRadioState(event.getCommand(), currentState);
      }
      return null;
   }
}
