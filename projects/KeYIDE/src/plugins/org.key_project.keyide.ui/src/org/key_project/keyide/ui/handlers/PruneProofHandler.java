package org.key_project.keyide.ui.handlers;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.common.ui.handler.AbstractSaveExecutionHandler;
import org.key_project.keyide.ui.providers.BranchFolder;
import org.key_project.util.eclipse.swt.SWTUtil;

import de.uka.ilkd.key.proof.Node;

// TODO: Document members in class PruneProofHandler
public class PruneProofHandler extends AbstractSaveExecutionHandler {
   @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
      ISelection selection = HandlerUtil.getCurrentSelection(event);
      Object[] elements = SWTUtil.toArray(selection);
      for (Object element : elements) {
          if (element instanceof Node) {
              Node node = (Node)element;
              node.proof().pruneProof(node);
          }
          else if (element instanceof BranchFolder) {
             Node node = ((BranchFolder)element).getChild();
             node.proof().pruneProof(node);
          }
      }
      return null;
   }
}
