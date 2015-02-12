package org.key_project.sed.ui.command;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.debug.ui.IDebugView;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.sed.ui.util.LogUtil;
import org.key_project.sed.ui.util.SEDUIUtil;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * Expands all elements below the selected elements in an {@link IDebugView}.
 * @author Martin Hentschel
 */
public class ExpandAllCommand extends AbstractHandler {
   /**
    * {@inheritDoc}
    */
   @Override
   public Object execute(ExecutionEvent event) throws ExecutionException {
      try {
         IWorkbenchPart part = HandlerUtil.getActivePart(event);
         if (part instanceof IDebugView) {
            IDebugView debugView = (IDebugView)part;
            SEDUIUtil.expandInDebugView(debugView.getSite().getPart(), 
                                        debugView, 
                                        SWTUtil.toList(HandlerUtil.getCurrentSelection(event)));
         }
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(HandlerUtil.getActiveShell(event), e);
      }
      return null;
   }
}
