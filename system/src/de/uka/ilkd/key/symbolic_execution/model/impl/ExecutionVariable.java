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

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.ApplyStrategy;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionValue;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.util.SideProofUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil.SiteProofVariableValueInput;

/**
 * The default implementation of {@link IExecutionVariable}.
 * @author Martin Hentschel
 */
public class ExecutionVariable extends AbstractExecutionVariable {
   /**
    * The parent {@link IExecutionNode} which provides this {@link ExecutionVariable}.
    */
   private final IExecutionNode<?> parentNode;
   
   /**
    * The {@link ExecutionValue} from which the array length was computed.
    */
   private final ExecutionValue lengthValue;

   /**
    * The possible values of this {@link IExecutionValue}.
    */
   private ExecutionValue[] values;

   /**
    * Constructor for a "normal" value.
    * @param parentNode The parent {@link IExecutionNode} which provides this {@link ExecutionVariable}.
    * @param programVariable The represented {@link IProgramVariable} which value is shown.
    * @param additionalCondition An optional additional condition to consider.
    */
   public ExecutionVariable(IExecutionNode<?> parentNode,
                            Node proofNode, 
                            PosInOccurrence modalityPIO, 
                            IProgramVariable programVariable,
                            Term additionalCondition) {
      this(parentNode, proofNode, modalityPIO, null, programVariable, additionalCondition);
   }
   
   /**
    * Constructor for a "normal" child value.
    * @param settings The {@link ITreeSettings} to use.
    * @param parentNode The parent {@link IExecutionNode} which provides this {@link ExecutionVariable}.
    * @param parentValue The parent {@link ExecutionValue} or {@code null} if not available.
    * @param programVariable The represented {@link IProgramVariable} which value is shown.
    * @param additionalCondition An optional additional condition to consider.
    */
   public ExecutionVariable(IExecutionNode<?> parentNode,
                            Node proofNode, 
                            PosInOccurrence modalityPIO, 
                            ExecutionValue parentValue, 
                            IProgramVariable programVariable,
                            Term additionalCondition) {
      super(parentNode.getSettings(), 
            parentNode.getMediator(), 
            proofNode, 
            programVariable, 
            parentValue, 
            -1, 
            additionalCondition,
            modalityPIO);
      assert programVariable != null;
      assert modalityPIO != null;
      this.parentNode = parentNode;
      this.lengthValue = null;
   }

   /**
    * Constructor for an array cell value.
    * @param parentNode The parent {@link IExecutionNode} which provides this {@link ExecutionVariable}.
    * @param parentValue The parent {@link ExecutionValue} or {@code null} if not available.
    * @param arrayIndex The index in the parent array.
    * @param lengthValue The {@link ExecutionValue} from which the array length was computed.
    * @param additionalCondition An optional additional condition to consider.
    */
   public ExecutionVariable(IExecutionNode<?> parentNode,
                            Node proofNode, 
                            PosInOccurrence modalityPIO, 
                            ExecutionValue parentValue, 
                            int arrayIndex,
                            ExecutionValue lengthValue,
                            Term additionalCondition) {
      super(parentNode.getSettings(), 
            parentNode.getMediator(), 
            proofNode, 
            null, 
            parentValue, 
            arrayIndex, 
            additionalCondition,
            modalityPIO);
      assert modalityPIO != null;
      this.parentNode = parentNode;
      this.lengthValue = lengthValue;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ExecutionValue[] getValues() throws ProofInputException {
      synchronized (this) {
         if (values == null) {
            values = lazyComputeValues();
         }
         return values;
      }
   }
   
   /**
    * Computes the value for {@link #getValues()}
    * lazily when the method is called the first time.
    * @throws ProofInputException Occurred Exception.
    */
   protected ExecutionValue[] lazyComputeValues() throws ProofInputException {
      if (!isDisposed()) {
         final Services services = getServices();
         final TermBuilder tb = services.getTermBuilder();
         // Start site proof to extract the value of the result variable.
         SiteProofVariableValueInput sequentToProve;
         Term siteProofSelectTerm = null;
         Term siteProofCondition = parentNode.getPathCondition();
         if (getAdditionalCondition() != null) {
            siteProofCondition = tb.and(siteProofCondition, getAdditionalCondition());
         }
         if (getParentValue() != null || SymbolicExecutionUtil.isStaticVariable(getProgramVariable())) {
            siteProofSelectTerm = createSelectTerm(services);
            if (getParentValue() != null) { // Is null at static variables
               siteProofCondition = tb.and(siteProofCondition, getParentValue().getCondition());
            }
            if (lengthValue != null) {
               siteProofCondition = tb.and(siteProofCondition, lengthValue.getCondition());
            }
            sequentToProve = SymbolicExecutionUtil.createExtractTermSequent(services, getProofNode(), getModalityPIO(), siteProofCondition, siteProofSelectTerm, true); 
         }
         else {
            sequentToProve = SymbolicExecutionUtil.createExtractVariableValueSequent(services, getProofNode(), getModalityPIO(), siteProofCondition, getProgramVariable());
         }
         ApplyStrategy.ApplyStrategyInfo info = SideProofUtil.startSideProof(getProof(), 
                                                                             sequentToProve.getSequentToProve(), 
                                                                             StrategyProperties.METHOD_NONE,
                                                                             StrategyProperties.LOOP_NONE,
                                                                             StrategyProperties.QUERY_OFF,
                                                                             StrategyProperties.SPLITTING_DELAYED,
                                                                             true);
         try {
            List<ExecutionValue> result = new ArrayList<ExecutionValue>(info.getProof().openGoals().size());
            // Group values of the branches
            Map<Term, List<Goal>> valueMap = new LinkedHashMap<Term, List<Goal>>();
            List<Goal> unknownValues = new LinkedList<Goal>();
            groupGoalsByValue(info.getProof().openGoals(), sequentToProve.getOperator(), siteProofSelectTerm, siteProofCondition, valueMap, unknownValues, services);
            // Instantiate child values
            for (Entry<Term, List<Goal>> valueEntry : valueMap.entrySet()) {
               Term value = valueEntry.getKey();
               // Format return vale
               String valueString = formatTerm(value, services);
               // Determine type
               String typeString = value.sort().toString();
               // Compute value condition
               Term condition = computeValueCondition(tb, valueEntry.getValue(), services);
               String conditionString = null;
               if (condition != null) {
                  conditionString = formatTerm(condition, services);
               }
               // Update result
               result.add(new ExecutionValue(getMediator(),
                                             getProofNode(),
                                             this,
                                             false,
                                             value,
                                             valueString,
                                             typeString,
                                             condition,
                                             conditionString));
            }
            // Instantiate unknown child values
            if (!unknownValues.isEmpty()) {
               // Compute value condition
               Term condition = computeValueCondition(tb, unknownValues, services);
               String conditionString = null;
               if (condition != null) {
                  conditionString = formatTerm(condition, services);
               }
               // Update result
               result.add(new ExecutionValue(getMediator(),
                                             getProofNode(),
                                             this,
                                             true,
                                             null,
                                             null,
                                             null,
                                             condition,
                                             conditionString));
            }
            // Return child values as result
            return result.toArray(new ExecutionValue[result.size()]);
         }
         finally {
            SideProofUtil.disposeOrStore("Value computation on node " + getProofNode().serialNr(), info);
         }
      }
      else {
         return null;
      }
   }

   /**
    * Groups all {@link Goal}s which provides the same value.
    * @param goals All available {@link Goal}s to group.
    * @param operator The {@link Operator} of the {@link Term} which provides the value.
    * @param services The {@link Services} to use.
    */
   protected void groupGoalsByValue(ImmutableList<Goal> goals, 
                                    Operator operator, 
                                    Term siteProofSelectTerm,
                                    Term siteProofCondition,
                                    Map<Term, List<Goal>> valueMap,
                                    List<Goal> unknownValues,
                                    Services services) throws ProofInputException {
      for (Goal goal : goals) {
         // Extract value
         Term value = SideProofUtil.extractOperatorValue(goal, operator);
         assert value != null;
         value = SymbolicExecutionUtil.replaceSkolemConstants(goal.sequent(), value, services);
         // Compute unknown flag if required
         boolean unknownValue = false;
         if (siteProofSelectTerm != null) {
            if (SymbolicExecutionUtil.isNullSort(value.sort(), services)) { 
               unknownValue = SymbolicExecutionUtil.isNull(services, getProofNode(), siteProofCondition, siteProofSelectTerm); // Check if the symbolic value is not null, if it fails the value is treated as unknown
            }
            else {
               unknownValue = SymbolicExecutionUtil.isNotNull(services, getProofNode(), siteProofCondition, siteProofSelectTerm); // Check if the symbolic value is not null, if it fails the value is treated as unknown
            }
         }
         // Add to result list
         if (unknownValue) {
            unknownValues.add(goal);
         }
         else {
            List<Goal> valueList = valueMap.get(value);
            if (valueList == null) {
               valueList = new LinkedList<Goal>();
               valueMap.put(value, valueList);
            }
            valueList.add(goal);
         }
      }
   }
   
   /**
    * Computes the combined path condition of all {@link Goal}s which is the
    * or combination of each path condition per {@link Goal}.
    * @param tb The {@link TermBuilder} to use passed to ensure that it is still available even if the {@link Proof} is disposed in between.
    * @param valueGoals The {@link Goal}s to compute combined path condition for.
    * @param services The {@link Services} to use.
    * @return The combined path condition.
    * @throws ProofInputException Occurred Exception.
    */
   protected Term computeValueCondition(TermBuilder tb, List<Goal> valueGoals, Services services) throws ProofInputException {
      if (!valueGoals.isEmpty()) {
         List<Term> pathConditions = new LinkedList<Term>();
         Proof proof = null;
         for (Goal valueGoal : valueGoals) {
            pathConditions.add(SymbolicExecutionUtil.computePathCondition(valueGoal.node(), false));
            proof = valueGoal.node().proof();
         }
         Term comboundPathCondition = tb.or(pathConditions);
         comboundPathCondition = SymbolicExecutionUtil.simplify(proof, comboundPathCondition);
         comboundPathCondition = SymbolicExecutionUtil.improveReadability(comboundPathCondition, services);
         return comboundPathCondition;
      }
      else {
         return tb.tt();
      }
   }
   
   /**
    * Creates recursive a term which can be used to determine the value
    * of {@link #getProgramVariable()}.
    * @param services The {@link Services} to use.
    * @return The created term.
    */
   protected Term createSelectTerm(Services services) {
      if (SymbolicExecutionUtil.isStaticVariable(getProgramVariable())) {
         // Static field access
         Function function = services.getTypeConverter().getHeapLDT().getFieldSymbolForPV((LocationVariable)getProgramVariable(), services);
         return services.getTermBuilder().staticDot(getProgramVariable().sort(), function);
      }
      else {
         if (getParentValue() == null) {
            // Direct access to a variable, so return it as term
            return services.getTermBuilder().var((ProgramVariable)getProgramVariable());
         }
         else {
            Term parentTerm = getParentValue().getVariable().createSelectTerm(services);
            if (getProgramVariable() != null) {
               if (services.getJavaInfo().getArrayLength() == getProgramVariable()) {
                  // Special handling for length attribute of arrays
                  Function function = services.getTypeConverter().getHeapLDT().getLength();
                  return services.getTermBuilder().func(function, parentTerm);
               }
               else {
                  // Field access on the parent variable
                  Function function = services.getTypeConverter().getHeapLDT().getFieldSymbolForPV((LocationVariable)getProgramVariable(), services);
                  return services.getTermBuilder().dot(getProgramVariable().sort(), parentTerm, function);
               }
            }
            else {
               // Special handling for array indices.
               Term idx = services.getTermBuilder().zTerm("" + getArrayIndex());
               return services.getTermBuilder().dotArr(parentTerm, idx);
            }
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ExecutionValue getParentValue() {
      return (ExecutionValue)super.getParentValue();
   }

   /**
    * Returns the parent {@link IExecutionNode} which provides this {@link ExecutionVariable}.
    * @return The parent {@link IExecutionNode} which provides this {@link ExecutionVariable}.
    */
   public IExecutionNode<?> getParentNode() {
      return parentNode;
   }
}