package de.uka.ilkd.key.symbolic_execution.strategy;

import de.uka.ilkd.key.proof.GoalChooserBuilder;
import de.uka.ilkd.key.proof.IGoalChooser;

/**
 * This {@link GoalChooserBuilder} creates a special {@link IGoalChooser}
 * for symbolic execution.
 * @author Martin Hentschel
 * @see SymbolicExecutionGoalChooser
 */
public class SymbolicExecutionGoalChooserBuilder implements GoalChooserBuilder {
   /**
    * The name of this goal chooser.
    */
   public static final String NAME = "Symbolic Execution Goal Chooser";

   /**
    * {@inheritDoc}
    */
   @Override
   public IGoalChooser create() {
      return new SymbolicExecutionGoalChooser();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public GoalChooserBuilder copy() {
      return new SymbolicExecutionGoalChooserBuilder();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String name() {
      return NAME;
   }
}
