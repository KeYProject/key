package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.SymbolicExecutionTermLabel;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * The {@link ITermLabelWorker} used during prove to define how a
 * {@link SymbolicExecutionTermLabel} is maintained.
 * @author Martin Hentschel
 */
public final class SymbolicExecutionTermLabelInstantiator extends AbstractSymbolicExecutionInstantiator {
   /**
    * The only instance of this class.
    */
   public static final SymbolicExecutionTermLabelInstantiator INSTANCE = new SymbolicExecutionTermLabelInstantiator();

   /**
    * Constructor to forbid multiple instances.
    */
   private SymbolicExecutionTermLabelInstantiator() {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected ITermLabel getTermLabel(Term applicationTerm) {
      return SymbolicExecutionUtil.getSymbolicExecutionLabel(applicationTerm);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return SymbolicExecutionTermLabel.NAME.toString();
   }
}
