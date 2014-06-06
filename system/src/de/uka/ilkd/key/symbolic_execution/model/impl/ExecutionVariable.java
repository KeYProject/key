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
import de.uka.ilkd.key.gui.ApplyStrategy;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStateNode;
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
public class ExecutionVariable extends AbstractExecutionElement implements IExecutionVariable {
   /**
    * The parent {@link IExecutionStateNode} which provides this {@link ExecutionVariable}.
    */
   private final IExecutionStateNode<?> parentNode;
   
   /**
    * The represented {@link IProgramVariable} which value is shown.
    */
   private final IProgramVariable programVariable;
   
   /**
    * The parent {@link ExecutionValue} or {@code null} if not available.
    */
   private final ExecutionValue parentValue;
   
   /**
    * The index in the parent array.
    */
   private final int arrayIndex;
   
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
    * @param parentNode The parent {@link IExecutionStateNode} which provides this {@link ExecutionVariable}.
    * @param programVariable The represented {@link IProgramVariable} which value is shown.
    */
   public ExecutionVariable(IExecutionStateNode<?> parentNode,
                            IProgramVariable programVariable) {
      this(parentNode, null, programVariable);
   }
   
   /**
    * Constructor for a "normal" child value.
    * @param settings The {@link ITreeSettings} to use.
    * @param parentNode The parent {@link IExecutionStateNode} which provides this {@link ExecutionVariable}.
    * @param parentValue The parent {@link ExecutionValue} or {@code null} if not available.
    * @param programVariable The represented {@link IProgramVariable} which value is shown.
    */
   public ExecutionVariable(IExecutionStateNode<?> parentNode,
                            ExecutionValue parentValue, 
                            IProgramVariable programVariable) {
      super(parentNode.getSettings(), parentNode.getMediator(), parentNode.getProofNode());
      assert programVariable != null;
      this.parentNode = parentNode;
      this.parentValue = parentValue;
      this.programVariable = programVariable;
      this.arrayIndex = -1;
      this.lengthValue = null;
   }

   /**
    * Constructor for an array cell value.
    * @param parentNode The parent {@link IExecutionStateNode} which provides this {@link ExecutionVariable}.
    * @param parentValue The parent {@link ExecutionValue} or {@code null} if not available.
    * @param arrayIndex The index in the parent array.
    * @param lengthValue The {@link ExecutionValue} from which the array length was computed.
    */
   public ExecutionVariable(IExecutionStateNode<?> parentNode,
                            ExecutionValue parentValue, 
                            int arrayIndex,
                            ExecutionValue lengthValue) {
      super(parentNode.getSettings(), parentNode.getMediator(), parentNode.getProofNode());
      this.programVariable = null;
      this.parentNode = parentNode;
      this.parentValue = parentValue;
      this.arrayIndex = arrayIndex;
      this.lengthValue = lengthValue;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() throws ProofInputException {
      IProgramVariable pv = getProgramVariable();
      if (pv != null) {
         return SymbolicExecutionUtil.getDisplayString(pv);
      }
      else {
         return "[" + arrayIndex + "]";
      }
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
      // Start site proof to extract the value of the result variable.
      SiteProofVariableValueInput sequentToProve;
      Term siteProofSelectTerm = null;
      Term siteProofCondition = parentNode.getPathCondition();
      if (getParentValue() != null || SymbolicExecutionUtil.isStaticVariable(getProgramVariable())) {
         siteProofSelectTerm = createSelectTerm();
         if (getParentValue() != null) { // Is null at static variables
            siteProofCondition = getServices().getTermBuilder().and(siteProofCondition, getParentValue().getCondition());
         }
         if (lengthValue != null) {
            siteProofCondition = getServices().getTermBuilder().and(siteProofCondition, lengthValue.getCondition());
         }
         sequentToProve = SymbolicExecutionUtil.createExtractTermSequent(getServices(), getProofNode(), siteProofCondition, siteProofSelectTerm, true); 
      }
      else {
         sequentToProve = SymbolicExecutionUtil.createExtractVariableValueSequent(getServices(), getProofNode(), siteProofCondition, getProgramVariable());
      }
      ApplyStrategy.ApplyStrategyInfo info = SideProofUtil.startSideProof(getProof(), 
                                                                          sequentToProve.getSequentToProve(), 
                                                                          StrategyProperties.METHOD_NONE,
                                                                          StrategyProperties.LOOP_NONE,
                                                                          StrategyProperties.QUERY_OFF,
                                                                          StrategyProperties.SPLITTING_DELAYED);
      try {
         List<ExecutionValue> result = new ArrayList<ExecutionValue>(info.getProof().openGoals().size());
         // Group values of the branches
         Map<Term, List<Goal>> valueMap = new LinkedHashMap<Term, List<Goal>>();
         List<Goal> unknownValues = new LinkedList<Goal>();
         groupGoalsByValue(info.getProof().openGoals(), sequentToProve.getOperator(), siteProofSelectTerm, siteProofCondition, valueMap, unknownValues);
         // Instantiate child values
         for (Entry<Term, List<Goal>> valueEntry : valueMap.entrySet()) {
            Term value = valueEntry.getKey();
            // Format return vale
            String valueString = formatTerm(value);
            // Determine type
            String typeString = value.sort().toString();
            // Compute value condition
            Term condition = computeValueCondition(valueEntry.getValue());
            String conditionString = null;
            if (condition != null) {
               conditionString = formatTerm(condition);
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
            Term condition = computeValueCondition(unknownValues);
            String conditionString = null;
            if (condition != null) {
               conditionString = formatTerm(condition);
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

   /**
    * Groups all {@link Goal}s which provides the same value.
    * @param goals All available {@link Goal}s to group.
    * @param operator The {@link Operator} of the {@link Term} which provides the value.
    */
   protected void groupGoalsByValue(ImmutableList<Goal> goals, 
                                    Operator operator, 
                                    Term siteProofSelectTerm,
                                    Term siteProofCondition,
                                    Map<Term, List<Goal>> valueMap,
                                    List<Goal> unknownValues) throws ProofInputException {
      for (Goal goal : goals) {
         // Extract value
         Term value = SideProofUtil.extractOperatorValue(goal, operator);
         assert value != null;
         value = SymbolicExecutionUtil.replaceSkolemConstants(goal.sequent(), value, getServices());
         // Compute unknown flag if required
         boolean unknownValue = false;
         if (siteProofSelectTerm != null) {
            if (SymbolicExecutionUtil.isNullSort(value.sort(), getServices())) { 
               unknownValue = SymbolicExecutionUtil.isNull(getServices(), getProofNode(), siteProofCondition, siteProofSelectTerm); // Check if the symbolic value is not null, if it fails the value is treated as unknown
            }
            else {
               unknownValue = SymbolicExecutionUtil.isNotNull(getServices(), getProofNode(), siteProofCondition, siteProofSelectTerm); // Check if the symbolic value is not null, if it fails the value is treated as unknown
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
    * @param valueGoals The {@link Goal}s to compute combined path condition for.
    * @return The combined path condition.
    * @throws ProofInputException Occurred Exception.
    */
   protected Term computeValueCondition(List<Goal> valueGoals) throws ProofInputException {
      if (!valueGoals.isEmpty()) {
         List<Term> pathConditions = new LinkedList<Term>();
         Proof proof = null;
         for (Goal valueGoal : valueGoals) {
            pathConditions.add(SymbolicExecutionUtil.computePathCondition(valueGoal.node(), false));
            proof = valueGoal.node().proof();
         }
         Term comboundPathCondition = getServices().getTermBuilder().or(pathConditions);
         comboundPathCondition = SymbolicExecutionUtil.simplify(proof, comboundPathCondition);
         comboundPathCondition = SymbolicExecutionUtil.improveReadability(comboundPathCondition, proof.getServices());
         return comboundPathCondition;
      }
      else {
         return getServices().getTermBuilder().tt();
      }
   }
   
   /**
    * Creates recursive a term which can be used to determine the value
    * of {@link #getProgramVariable()}.
    * @return The created term.
    */
   protected Term createSelectTerm() {
      if (SymbolicExecutionUtil.isStaticVariable(getProgramVariable())) {
         // Static field access
         Function function = getServices().getTypeConverter().getHeapLDT().getFieldSymbolForPV((LocationVariable)getProgramVariable(), getServices());
         return getServices().getTermBuilder().staticDot(getProgramVariable().sort(), function);
      }
      else {
         if (getParentValue() == null) {
            // Direct access to a variable, so return it as term
            return getServices().getTermBuilder().var((ProgramVariable)getProgramVariable());
         }
         else {
            Term parentTerm = getParentValue().getVariable().createSelectTerm();
            if (programVariable != null) {
               if (getServices().getJavaInfo().getArrayLength() == getProgramVariable()) {
                  // Special handling for length attribute of arrays
                  Function function = getServices().getTypeConverter().getHeapLDT().getLength();
                  return getServices().getTermBuilder().func(function, parentTerm);
               }
               else {
                  // Field access on the parent variable
                  Function function = getServices().getTypeConverter().getHeapLDT().getFieldSymbolForPV((LocationVariable)getProgramVariable(), getServices());
                  return getServices().getTermBuilder().dot(getProgramVariable().sort(), parentTerm, function);
               }
            }
            else {
               // Special handling for array indices.
               Term idx = getServices().getTermBuilder().zTerm("" + arrayIndex);
               return getServices().getTermBuilder().dotArr(parentTerm, idx);
            }
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IProgramVariable getProgramVariable() {
      return programVariable;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getArrayIndex() {
      return arrayIndex;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isArrayIndex() {
      return getArrayIndex() >= 0;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getElementType() {
      return "Variable";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ExecutionValue getParentValue() {
      return parentValue;
   }
   
   /**
    * Returns the parent {@link IExecutionStateNode} which provides this {@link ExecutionVariable}.
    * @return The parent {@link IExecutionStateNode} which provides this {@link ExecutionVariable}.
    */
   public IExecutionStateNode<?> getParentNode() {
      return parentNode;
   }
}