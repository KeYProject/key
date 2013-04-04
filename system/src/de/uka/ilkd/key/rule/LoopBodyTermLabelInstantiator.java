package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.LoopBodyTermLabel;
import de.uka.ilkd.key.logic.SymbolicExecutionTermLabel;
import de.uka.ilkd.key.logic.Term;

/**
 * The {@link ITermLabelWorker} used during prove to define how a
 * {@link SymbolicExecutionTermLabel} is maintained.
 * @author Martin Hentschel
 */
public final class LoopBodyTermLabelInstantiator extends AbstractSymbolicExecutionInstantiator {
   /**
    * The only instance of this class.
    */
   public static final LoopBodyTermLabelInstantiator INSTANCE = new LoopBodyTermLabelInstantiator();

   /**
    * Constructor to forbid multiple instances.
    */
   private LoopBodyTermLabelInstantiator() {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected ITermLabel getTermLabel(Term applicationTerm) {
      return LoopBodyTermLabel.INSTANCE;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return LoopBodyTermLabel.NAME.toString();
   }
}
