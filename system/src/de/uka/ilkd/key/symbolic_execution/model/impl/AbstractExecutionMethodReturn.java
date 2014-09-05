package de.uka.ilkd.key.symbolic_execution.model.impl;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBaseMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * The default implementation of {@link IExecutionBaseMethodReturn}.
 * @author Martin Hentschel
 */
public abstract class AbstractExecutionMethodReturn<S extends SourceElement> extends AbstractExecutionNode<S> implements IExecutionBaseMethodReturn<S> {
   /**
    * The {@link IExecutionMethodCall} which is now returned.
    */
   private final ExecutionMethodCall methodCall;

   /**
    * The signature.
    */
   private String signature;
   
   /**
    * The method return condition to reach this node from its calling {@link IExecutionMethodCall}.
    */
   private Term methodReturnCondition;
   
   /**
    * The human readable method return condition to reach this node from its calling {@link IExecutionMethodCall}.
    */
   private String formatedMethodReturnCondition;
   
   /**
    * Constructor.
    * @param settings The {@link ITreeSettings} to use.
    * @param mediator The used {@link KeYMediator} during proof.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    * @param methodCall The {@link IExecutionMethodCall} which is now returned.
    */
   public AbstractExecutionMethodReturn(ITreeSettings settings, 
                                        KeYMediator mediator, 
                                        Node proofNode, 
                                        ExecutionMethodCall methodCall) {
      super(settings, mediator, proofNode);
      assert methodCall != null;
      this.methodCall = methodCall;
      this.methodCall.addMethodReturn(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IExecutionMethodCall getMethodCall() {
      return methodCall;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getSignature() throws ProofInputException {
      if (signature == null) {
         signature = lazyComputeSignature();
      }
      return signature;
   }

   /**
    * Computes the signature lazily when
    * {@link #getSignature()} is called the first time.
    * @return The name including the return value.
    * @throws Occurred Exception.
    */
   protected abstract String lazyComputeSignature() throws ProofInputException;


   /**
    * {@inheritDoc}
    */
   @Override
   public Term getMethodReturnCondition() throws ProofInputException {
      if (methodReturnCondition == null) {
         lazyComputeMethodReturnCondition();
      }
      return methodReturnCondition;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getFormatedMethodReturnCondition() throws ProofInputException {
      if (methodReturnCondition == null) {
         lazyComputeMethodReturnCondition();
      }
      return formatedMethodReturnCondition;
   }

   /**
    * Computes the path condition lazily when {@link #getMethodReturnCondition()}
    * or {@link #getFormatedMethodReturnCondition()} is called the first time.
    * @throws ProofInputException Occurred Exception
    */
   protected void lazyComputeMethodReturnCondition() throws ProofInputException {
      if (!isDisposed()) {
         final Services services = getServices();
         // Collect branch conditions
         List<Term> bcs = new LinkedList<Term>();
         AbstractExecutionNode<?> parent = getParent();
         while (parent != null && parent != methodCall) {
            if (parent instanceof IExecutionBranchCondition) {
               bcs.add(((IExecutionBranchCondition)parent).getBranchCondition());
            }
            parent = parent.getParent();
         }
         // Add current branch condition to path
         methodReturnCondition = services.getTermBuilder().and(bcs);
         // Simplify path condition
         methodReturnCondition = SymbolicExecutionUtil.simplify(getProof(), methodReturnCondition);
         methodReturnCondition = SymbolicExecutionUtil.improveReadability(methodReturnCondition, services);
         // Format path condition
         formatedMethodReturnCondition = formatTerm(methodReturnCondition, services);
      }
   }
}
