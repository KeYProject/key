// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
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

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.SymbolicExecutionTermLabel;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.ApplyStrategy;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturnValue;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;
import de.uka.ilkd.key.symbolic_execution.util.SideProofUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil.SiteProofVariableValueInput;
import de.uka.ilkd.key.util.MiscTools;

/**
 * The default implementation of {@link IExecutionMethodReturn}.
 * @author Martin Hentschel
 */
public class ExecutionMethodReturn extends AbstractExecutionMethodReturn<SourceElement> implements IExecutionMethodReturn {
   /**
    * The node name with signature including the return value.
    */
   private String signatureIncludingReturnValue;
   
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
    * @param settings The {@link ITreeSettings} to use.
    * @param mediator The used {@link KeYMediator} during proof.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    * @param methodCall The {@link IExecutionMethodCall} which is now returned.
    */
   public ExecutionMethodReturn(ITreeSettings settings,
                                KeYMediator mediator, 
                                Node proofNode, 
                                ExecutionMethodCall methodCall) {
      super(settings, mediator, proofNode, methodCall);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() throws ProofInputException {
      return createMethodReturnName(null, computeCalledMethodName());
   }
   
   /**
    * Computes the name of the called method.
    * @return The name of the called method.
    */
   protected String computeCalledMethodName() {
      MethodReference explicitConstructorMR = getMethodCall().getExplicitConstructorMethodReference();
      return explicitConstructorMR != null ?
             explicitConstructorMR.getMethodName().toString() :
             getMethodCall().getProgramMethod().getName();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeSignature() throws ProofInputException {
      return createMethodReturnName(null, computeCalledMethodSignature());
   }
   
   /**
    * Computes the signature of the called method.
    * @return The signature of the called method.
    */
   protected String computeCalledMethodSignature() throws ProofInputException {
      MethodReference explicitConstructorMR = getMethodCall().getExplicitConstructorMethodReference();
      String call = explicitConstructorMR != null ?
                    explicitConstructorMR.toString() :
                    getMethodCall().getMethodReference().toString();
      if (call.endsWith(";")) {
         call = call.substring(0, call.length() - 1);
      }
      return call;
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
         return createMethodReturnName(null, computeCalledMethodName());
      }
      else if (returnValues.length == 1) {
         return createMethodReturnName(returnValues[0].getName() + " ", computeCalledMethodName());
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
         return createMethodReturnName(sb.toString(), computeCalledMethodName());
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getSignatureIncludingReturnValue() throws ProofInputException {
      if (signatureIncludingReturnValue == null) {
         signatureIncludingReturnValue = lazyComputeSigntureIncludingReturnValue();
      }
      return signatureIncludingReturnValue;
   }

   /**
    * Computes the signature including the return value lazily when
    * {@link #getNameIncludingReturnValue()} is called the first time.
    * @return The name including the return value.
    * @throws Occurred Exception.
    */
   protected String lazyComputeSigntureIncludingReturnValue() throws ProofInputException {
      IExecutionMethodReturnValue[] returnValues = getReturnValues();
      if (returnValues.length == 0) {
         return createMethodReturnName(null, computeCalledMethodSignature());
      }
      else if (returnValues.length == 1) {
         return createMethodReturnName(returnValues[0].getName() + " ", computeCalledMethodSignature());
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
         return createMethodReturnName(sb.toString(), computeCalledMethodSignature());
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
      if (!isDisposed()) {
         final Services services = getServices();
         // Check if a result variable is available
         MethodBodyStatement mbs = getMethodCall().getActiveStatement();
         IProgramVariable resultVar = mbs.getResultVariable();
         // Create a temporary result variable for non void methods in case that it is missing in method frame
         if (resultVar == null) {
            IProgramMethod pm = mbs.getProgramMethod(services);
            if (!pm.isVoid()) {
               resultVar = new LocationVariable(new ProgramElementName(services.getTermBuilder().newName("TmpResultVar")), pm.getReturnType());
            }
         }
         if (resultVar != null) {
            // Search the node with applied rule "methodCallReturn" which provides the required updates
            Node methodReturnNode = findMethodReturnNode(getProofNode());
            if (methodReturnNode != null) {
               // Start site proof to extract the value of the result variable.
               SiteProofVariableValueInput input = SymbolicExecutionUtil.createExtractReturnVariableValueSequent(services,
                                                                                                                 mbs.getBodySourceAsTypeReference(),
                                                                                                                 mbs.getProgramMethod(services),
                                                                                                                 mbs.getDesignatedContext(), 
                                                                                                                 methodReturnNode,
                                                                                                                 getProofNode(),
                                                                                                                 resultVar);
               ApplyStrategy.ApplyStrategyInfo info = SideProofUtil.startSideProof(getProof(), 
                                                                                   input.getSequentToProve(), 
                                                                                   StrategyProperties.METHOD_NONE,
                                                                                   StrategyProperties.LOOP_NONE,
                                                                                   StrategyProperties.QUERY_OFF,
                                                                                   StrategyProperties.SPLITTING_NORMAL,
                                                                                   true);
               try {
                  if (info.getProof().openGoals().size() == 1) {
                     Goal goal = info.getProof().openGoals().head();
                     Term returnValue = SideProofUtil.extractOperatorValue(goal, input.getOperator());
                     assert returnValue != null;
                     returnValue = SymbolicExecutionUtil.replaceSkolemConstants(goal.sequent(), returnValue, services);
                     return new IExecutionMethodReturnValue[] {new ExecutionMethodReturnValue(getSettings(), getMediator(), getProofNode(), getModalityPIO(), returnValue, null)};
                  }
                  else {
                     // Group equal values of different branches
                     Map<Term, List<Node>> valueNodeMap = new LinkedHashMap<Term, List<Node>>();
                     for (Goal goal : info.getProof().openGoals()) {
                        Term returnValue = SideProofUtil.extractOperatorValue(goal, input.getOperator());
                        assert returnValue != null;
                        returnValue = SymbolicExecutionUtil.replaceSkolemConstants(goal.node().sequent(), returnValue, services);
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
                        return new IExecutionMethodReturnValue[] {new ExecutionMethodReturnValue(getSettings(), getMediator(), getProofNode(), getModalityPIO(), returnValue, null)};
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
                           Term condition = services.getTermBuilder().or(conditions);
                           if (conditions.size() >= 2) {
                              condition = SymbolicExecutionUtil.simplify(info.getProof(), condition);
                           }
                           condition = SymbolicExecutionUtil.improveReadability(condition, info.getProof().getServices());
                           result[i] = new ExecutionMethodReturnValue(getSettings(), getMediator(), getProofNode(), getModalityPIO(), entry.getKey(), condition);
                           i++;
                        }
                        return result;
                     }
                  }
               }
               finally {
                  SideProofUtil.disposeOrStore("Return value computation on method return node " + methodReturnNode.serialNr() + ".", info);
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
      else {
         return new IExecutionMethodReturnValue[0];
      }
   }
   
   /**
    * Searches from the given {@link Node} the parent which applies
    * the rule "methodCallReturn" in the same modality.
    * @param node The {@link Node} to start search from.
    * @return The found {@link Node} with rule "methodCallReturn" or {@code null} if no node was found.
    */
   protected Node findMethodReturnNode(Node node) {
      Node resultNode = null;
      SymbolicExecutionTermLabel origianlLabel = SymbolicExecutionUtil.getSymbolicExecutionLabel(node.getAppliedRuleApp());
      if (origianlLabel != null) {
         while (node != null && resultNode == null) {
            if ("methodCallReturn".equals(MiscTools.getRuleDisplayName(node))) {
               SymbolicExecutionTermLabel currentLabel = SymbolicExecutionUtil.getSymbolicExecutionLabel(node.getAppliedRuleApp());
               if (currentLabel != null && origianlLabel.equals(currentLabel)) {
                  resultNode = node;
               }
            }
            node = node.parent();
         }
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
    * {@inheritDoc}
    */
   @Override
   protected IExecutionConstraint[] lazyComputeConstraints() {
      return SymbolicExecutionUtil.createExecutionConstraints(this);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getElementType() {
      return "Method Return";
   }
}