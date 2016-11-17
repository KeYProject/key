package org.key_project.keyide.ui.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.keyide.ui.providers.BranchFolder;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.eclipse.swt.SWTUtil;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

/**
 * Basic implementation to enable/disable {@link Goal}s below a selected {@link Node}.
 * @author Martin Hentschel
 */
public abstract class AbstractGoalsHandler extends AbstractHandler {
   /**
    * {@inheritDoc}
    */
   @Override
   public Object execute(ExecutionEvent event) throws ExecutionException {
      ISelection selection = HandlerUtil.getCurrentSelection(event);
      Object[] selectedElements = SWTUtil.toArray(selection);
      for (Object element : selectedElements) {
         if (element instanceof BranchFolder) {
            element = ((BranchFolder) element).getChild();
         }
         if (element instanceof Node) {
            Node node = (Node) element;
            Proof proof = node.proof();
            if (!proof.isDisposed()) {
               changeGoals(proof.getSubtreeGoals(node));
            }
         }
         else if (element instanceof Proof) {
            Proof proof = (Proof) element;
            if (!proof.isDisposed()) {
               changeGoals(proof.getSubtreeGoals(proof.root()));
            }
         }
      }
      return null;
   }

   /**
    * Changes the state of the given {@link Goal}s.
    * @param goals The {@link Goal}s to change.
    */
   protected void changeGoals(ImmutableList<Goal> goals) {
      for (Goal goal : goals) {
         changeGoal(goal);
      }
   }

   /**
    * Changes the state of the given {@link Goal}.
    * @param goal The {@link Goal} to change.
    */
   protected abstract void changeGoal(Goal goal);
}
