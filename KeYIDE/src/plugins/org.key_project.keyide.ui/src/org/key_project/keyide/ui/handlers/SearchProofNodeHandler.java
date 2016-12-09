package org.key_project.keyide.ui.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.keyide.ui.util.IProofNodeSearchSupport;

/**
 * Calls {@link IProofNodeSearchSupport#openSearchPanel()} on the active {@link IWorkbenchPart}.
 * @author Martin Hentschel
 */
public class SearchProofNodeHandler extends AbstractHandler {
   /**
    * {@inheritDoc}
    */
   @Override
   public Object execute(ExecutionEvent event) throws ExecutionException {
      IWorkbenchPart part = HandlerUtil.getActivePart(event);
      if (part != null) {
         IProofNodeSearchSupport support = (IProofNodeSearchSupport) part.getAdapter(IProofNodeSearchSupport.class);
         if (support != null) {
            support.openSearchPanel();
         }
      }
      return null;
   }
}
