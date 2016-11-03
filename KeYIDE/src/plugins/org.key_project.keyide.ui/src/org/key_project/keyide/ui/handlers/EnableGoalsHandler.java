package org.key_project.keyide.ui.handlers;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;

/**
 * Handler to enable all {@link Goal}s below the currently selected {@link Node}.
 * @author Martin Hentschel
 */
public class EnableGoalsHandler extends AbstractGoalsHandler {
   /**
    * {@inheritDoc}
    */
   @Override
   protected void changeGoal(Goal goal) {
      goal.setEnabled(true);
   }
}
