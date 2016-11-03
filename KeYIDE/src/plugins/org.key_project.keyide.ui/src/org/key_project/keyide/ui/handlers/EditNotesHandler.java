package org.key_project.keyide.ui.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.keyide.ui.providers.BranchFolder;
import org.key_project.keyide.ui.wizard.EditNotesWizard;
import org.key_project.util.eclipse.swt.SWTUtil;

import de.uka.ilkd.key.proof.Node;

/**
 * Handler to open the {@link EditNotesWizard} to annotate selected {@link Node}s.
 * @author Martin Hentschel
 */
public class EditNotesHandler extends AbstractHandler {
   /**
    * {@inheritDoc}
    */
   @Override
   public Object execute(ExecutionEvent event) throws ExecutionException {
      Shell activeShell = HandlerUtil.getActiveShell(event);
      ISelection selection = HandlerUtil.getCurrentSelection(event);
      Object[] selectedElements = SWTUtil.toArray(selection);
      for (Object element : selectedElements) {
         if (element instanceof BranchFolder) {
            element = ((BranchFolder) element).getChild();
         }
         if (element instanceof Node) {
            Node node = (Node) element;
            EditNotesWizard.openWizard(activeShell, node);
         }
      }
      return null;
   }
}
