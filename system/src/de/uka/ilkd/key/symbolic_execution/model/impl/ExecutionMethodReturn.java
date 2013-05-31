// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.model.impl;

import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uka.ilkd.key.gui.ApplyStrategy;
import de.uka.ilkd.key.gui.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturnValue;
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
    * The possible return values.
    */
   private IExecutionMethodReturnValue[] returnValues;
   
   /**
    * Constructor.
    * @param mediator The used {@link KeYMediator} during proof.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    * @param methodCall The {@link IExecutionMethodCall} which is now returned.
    */
   public ExecutionMethodReturn(KeYMediator mediator, Node proofNode, IExecutionMethodCall methodCall) {
      super(mediator, proofNode);
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
   protected String lazyComputeName() throws ProofInputException {
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
      IExecutionMethodReturnValue[] returnValues = getReturnValues();
      if (returnValues.length == 0) {
         return createMethodReturnName(null, getMethodCall().getName());
      }
      else if (returnValues.length == 1) {
         return createMethodReturnName(returnValues[0].getName() + " ", getMethodCall().getName());
      }
      else {
         StringBuilder sb = new StringBuilder();
         sb.append('\n');
         boolean afterFirst = false;
         for (IExecutionMethodReturnValue value : returnValues) {
            if (afterFirst) {
               sb.append(", \n");
            }
            else {
               afterFirst = true;
            }
            sb.append('\t');
            sb.append(value.getName());
         }
         sb.append('\n');
         return createMethodReturnName(sb.toString(), getMethodCall().getName());
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IExecutionMethodReturnValue[] getReturnValues() throws ProofInputException {
      if (returnValues == null) {
         returnValues = lazyComputeReturnValues();
      }
      return returnValues;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isReturnValuesComputed() {
      return returnValues != null;
   }
   
   /**
    * Computes the return value lazily when
    * {@link #getReturnValue()} is called the first time.
    * @return The return value.
    * @throws ProofInputException Occurred Exception.
    */
   protected IExecutionMethodReturnValue[] lazyComputeReturnValues() throws ProofInputException {
      // Check if a result variable is available
      MethodBodyStatement mbs = getMethodCall().getActiveStatement();
      IProgramVariable resultVar = mbs.getResultVariable();
      if (resultVar != null) {
         // Search the node with applied rule "methodCallReturn" which provides the required updates
         Node methodReturnNode = findMethodReturnNode(getProofNode());
         if (methodReturnNode != null) {
            // Start site proof to extract the value of the result variable.
            SiteProofVariableValueInput input = SymbolicExecutionUtil.createExtractReturnVariableValueSequent(getServices(),
                                                                                                              mbs.getBodySourceAsTypeReference(),
                                                                                                              mbs.getProgramMethod(getServices()),
                                                                                                              mbs.getDesignatedContext(), 
                                                                                                              methodReturnNode,
                                                                                                              getProofNode(),
                                                                                                              resultVar);
            ApplyStrategy.ApplyStrategyInfo info = SymbolicExecutionUtil.startSideProof(getProof(), input.getSequentToProve(), StrategyProperties.SPLITTING_NORMAL);
            try {
               if (info.getProof().openGoals().size() == 1) {
                  Term returnValue = SymbolicExecutionUtil.extractOperatorValue(info.getProof().openGoals().head(), input.getOperator());
                  assert returnValue != null;
                  return new IExecutionMethodReturnValue[] {new ExecutionMethodReturnValue(getMediator(), getProofNode(), returnValue, null)};
               }
               else {
                  // Group equal values of different branches
                  Map<Term, List<Node>> valueNodeMap = new LinkedHashMap<Term, List<Node>>();
                  for (Goal goal : info.getProof().openGoals()) {
                     Term returnValue = SymbolicExecutionUtil.extractOperatorValue(goal, input.getOperator());
                     assert returnValue != null;
                     List<Node> nodeList = valueNodeMap.get(returnValue);
                     if (nodeList == null) {
                        nodeList = new LinkedList<Node>();
                        valueNodeMap.put(returnValue, nodeList);
                     }
                     nodeList.add(goal.node());
                  }
                  // Create result
                  if (valueNodeMap.size() == 1) {
                     Term returnValue = valueNodeMap.keySet().iterator().next();
                     return new IExecutionMethodReturnValue[] {new ExecutionMethodReturnValue(getMediator(), getProofNode(), returnValue, null)};
                  }
                  else {
                     IExecutionMethodReturnValue[] result = new IExecutionMethodReturnValue[valueNodeMap.size()];
                     int i = 0;
                     for (Entry<Term, List<Node>> entry : valueNodeMap.entrySet()) {
                        List<Term> conditions = new LinkedList<Term>();
                        for (Node node : entry.getValue()) {
                           Term condition = SymbolicExecutionUtil.computePathCondition(node, false);
                           conditions.add(condition);
                        }
                        Term condition = TermBuilder.DF.or(conditions);
                        condition = SymbolicExecutionUtil.simplify(info.getProof(), condition);
                        result[i] = new ExecutionMethodReturnValue(getMediator(), getProofNode(), entry.getKey(), condition);
                        i++;
                     }
                     return result;
                  }
               }
            }
            finally {
               info.getProof().dispose();
            }
         }
         else {
            return new IExecutionMethodReturnValue[0];
         }
      }
      else {
         return new IExecutionMethodReturnValue[0];
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
             (returnValue != null ? " " + returnValue + "as result" : "") +
             (!JavaUtil.isTrimmedEmpty(methodName) ? " of " + methodName : "") +
             INTERNAL_NODE_NAME_END;
   }
   
   /**
    * Starts a site proof for the given {@link Sequent}.
    * @param sequentToProve The {@link Sequent} to prove.
    * @return The proof result represented as {@link ApplyStrategyInfo} instance.
    * @throws ProofInputException Occurred Exception
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
