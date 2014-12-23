package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;

/**
 * The default implementation of {@link IExecutionConstraint}.
 * @author Martin Hentschel
 */
public class ExecutionConstraint extends AbstractExecutionElement implements IExecutionConstraint {
   /**
    * The {@link Term} representing the constraint.
    */
   private final Term term;
   
   /**
    * The {@link PosInOccurrence} of the modality of interest.
    */
   private final PosInOccurrence modalityPIO;

   /**
    * Constructor.
    * @param settings The {@link ITreeSettings} to use.
    * @param mediator The used {@link KeYMediator} during proof.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    * @param term The {@link Term} representing the constraint.
    */
   public ExecutionConstraint(ITreeSettings settings, KeYMediator mediator, Node proofNode, PosInOccurrence modalityPIO, Term term) {
      super(settings, mediator, proofNode);
      assert term != null;
      assert modalityPIO != null;
      this.term = term;
      this.modalityPIO = modalityPIO;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() throws ProofInputException {
      return formatTerm(term, getServices());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getElementType() {
      return "Constraint";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Term getTerm() {
      return term;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public PosInOccurrence getModalityPIO() {
      return modalityPIO;
   }
}
