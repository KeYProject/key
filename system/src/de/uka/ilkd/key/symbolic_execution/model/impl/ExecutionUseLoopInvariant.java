package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionUseLoopInvariant;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * The default implementation of {@link IExecutionUseLoopInvariant}.
 * @author Martin Hentschel
 */
public class ExecutionUseLoopInvariant extends AbstractExecutionStateNode<SourceElement> implements IExecutionUseLoopInvariant {
   /**
    * Constructor.
    * @param mediator The used {@link KeYMediator} during proof.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    */
   public ExecutionUseLoopInvariant(KeYMediator mediator, Node proofNode) {
      super(mediator, proofNode);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() {
      return getLoopInvariant().getPlainText(getServices());
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getElementType() {
      return "Use Loop Invariant";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected IExecutionVariable[] lazyComputeVariables() {
      return SymbolicExecutionUtil.createExecutionVariables(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public LoopInvariant getLoopInvariant() {
      return ((LoopInvariantBuiltInRuleApp)getProofNode().getAppliedRuleApp()).getInvariant();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public While getLoopStatement() {
      return ((LoopInvariantBuiltInRuleApp)getProofNode().getAppliedRuleApp()).getLoopStatement();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isInitiallyValid() {
      boolean initiallyValid = false;
      if (getProofNode().childrenCount() >= 1) {
         initiallyValid = getProofNode().child(0).isClosed();
      }
      return initiallyValid;
   }
}
