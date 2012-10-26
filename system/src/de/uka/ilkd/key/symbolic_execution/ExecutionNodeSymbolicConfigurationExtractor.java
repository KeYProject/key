package de.uka.ilkd.key.symbolic_execution;

import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Special {@link SymbolicConfigurationExtractor} for {@link IExecutionNode}s.
 * @author Martin Hentschel
 */
public class ExecutionNodeSymbolicConfigurationExtractor extends SymbolicConfigurationExtractor {
   /**
    * The {@link IExecutionNode} to extract configurations from.
    */
   private IExecutionNode executionNode;

   /**
    * Constructor.
    * @param executionNode The {@link IExecutionNode} to extract configurations from.
    */
   public ExecutionNodeSymbolicConfigurationExtractor(IExecutionNode executionNode) {
      super(executionNode.getProofNode());
      this.executionNode = executionNode;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String computeInitialStateName() {
      try {
         return SymbolicExecutionUtil.getRoot(executionNode).getName() + " resulting in " + computeCurrentStateName();
      }
      catch (ProofInputException e) {
         return e.getMessage();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String computeCurrentStateName() {
      try {
         return executionNode.getName();
      }
      catch (ProofInputException e) {
         return e.getMessage();
      }
   }
}
