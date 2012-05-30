package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.gui.ApplyStrategy;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil.SiteProofVariableValueInput;
import de.uka.ilkd.key.util.MiscTools;

/**
 * The default implementation of {@link IExecutionMethodReturn}.
 * @author Martin Hentschel
 */
public class ExecutionMethodReturn extends AbstractExecutionStateNode<SourceElement> implements IExecutionMethodReturn {
   /**
    * The {@link IExecutionMethodCall} which is now returned.
    */
   private IExecutionMethodCall methodCall;
   
   /**
    * The node name including the return value.
    */
   private String nameIncludingReturnValue;
   
   /**
    * The return value.
    */
   private Term returnValue;
   
   /**
    * The return value formated for the user.
    */
   private String formatedReturnValue;
   
   /**
    * Constructor.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    * @param methodCall The {@link IExecutionMethodCall} which is now returned.
    */
   public ExecutionMethodReturn(Node proofNode, IExecutionMethodCall methodCall) {
      super(proofNode);
      assert methodCall != null;
      this.methodCall = methodCall;
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
   protected String lazyComputeName() {
      return createMethodReturnName(null, getMethodCall().getName());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getNameIncludingReturnValue() throws ProofInputException {
      if (nameIncludingReturnValue == null) {
         nameIncludingReturnValue = lazyComputeNameIncludingReturnValue();
      }
      return nameIncludingReturnValue;
   }

   /**
    * Computes the name including the return value lazily when
    * {@link #getNameIncludingReturnValue()} is called the first time.
    * @return The name including the return value.
    * @throws Occurred Exception.
    */
   protected String lazyComputeNameIncludingReturnValue() throws ProofInputException {
      return createMethodReturnName(getFormatedReturnValue(), getMethodCall().getName());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getFormatedReturnValue() throws ProofInputException {
      if (returnValue == null) {
         lazyComputeReturnValue();
      }
      return formatedReturnValue;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   // TODO: Return value can be unknown in SET, e.g. quotient in TryCatchFinally test
   public Term getReturnValue() throws ProofInputException {
      if (returnValue == null) {
         lazyComputeReturnValue();
      }
      return returnValue;
   }
   
   /**
    * Computes the return value lazily when
    * {@link #getReturnValue()} is called the first time.
    * @return The return value.
    * @throws ProofInputException Occurred Exception.
    */
   protected void lazyComputeReturnValue() throws ProofInputException {
      // Check if a result variable is available
      MethodBodyStatement mbs = getMethodCall().getActiveStatement();
      IProgramVariable resultVar = mbs.getResultVariable();
      if (resultVar != null) {
         // Search the node with applied rule "methodCallReturn" which provides the required updates
         Node methodReturnNode = findMethodReturnNode(getProofNode());
         if (methodReturnNode != null) {
            // Start site proof to extract the value of the result variable.
            SiteProofVariableValueInput sequentToProve = SymbolicExecutionUtil.createExtractReturnVariableValueSequent(getServices(),
                                                                                                                       mbs.getBodySourceAsTypeReference(),  
                                                                                                                       mbs.getDesignatedContext(), 
                                                                                                                       methodReturnNode, 
                                                                                                                       resultVar);
            ApplyStrategy.ApplyStrategyInfo info = SymbolicExecutionUtil.startSideProof(getProof(), sequentToProve.getSequentToProve());
            returnValue = SymbolicExecutionUtil.extractOperatorValue(info, sequentToProve.getOperator());
            assert returnValue != null;
            // Format return vale
            StringBuffer sb = ProofSaver.printTerm(returnValue, getServices(), true);
            formatedReturnValue = sb.toString();
         }
      }
   }
   
   /**
    * Searches from the given {@link Node} the parent which applies
    * the rule "methodCallReturn".
    * @param node The {@link Node} to start search from.
    * @return The found {@link Node} with rule "methodCallReturn" or {@code null} if no node was found.
    */
   protected Node findMethodReturnNode(Node node) {
      Node resultNode = null;
      while (node != null && resultNode == null) {
         if ("methodCallReturn".equals(MiscTools.getRuleDisplayName(node))) {
            resultNode = node;
         }
         node = node.parent();
      }
      return resultNode;
   }

   /**
    * Creates the human readable name which is shown in {@link IExecutionMethodReturn} instances.
    * @param returnValue The return value.
    * @param methodName The name of the method that is completely executed.
    * @return The created human readable name.
    */
   public static String createMethodReturnName(Object returnValue, String methodName) {
      return INTERNAL_NODE_NAME_START + "return" +
             (returnValue != null ? " '" + returnValue + "' as result" : "") +
             (!JavaUtil.isTrimmedEmpty(methodName) ? " of " + methodName : "") +
             INTERNAL_NODE_NAME_END;
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
   public String getElementType() {
      return "Method Return";
   }
}
