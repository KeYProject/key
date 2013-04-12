package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.LoopInvariantNormalBehaviorTermLabel;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;

/**
 * The {@link ITermLabelWorker} used during prove to define how a
 * {@link LoopInvariantNormalBehaviorTermLabel} is maintained.
 * @author Martin Hentschel
 */
public final class LoopInvariantNormalBehaviorTermLabelInstantiator extends AbstractSymbolicExecutionInstantiator {
   /**
    * The only instance of this class.
    */
   public static final LoopInvariantNormalBehaviorTermLabelInstantiator INSTANCE = new LoopInvariantNormalBehaviorTermLabelInstantiator();

   /**
    * Constructor to forbid multiple instances.
    */
   private LoopInvariantNormalBehaviorTermLabelInstantiator() {
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean checkOperator(Operator newTermOp) {
      return Junctor.IMP == newTermOp;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected ITermLabel getTermLabel(Term applicationTerm) {
      return LoopInvariantNormalBehaviorTermLabel.INSTANCE;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return LoopInvariantNormalBehaviorTermLabel.NAME.toString();
   }
}
