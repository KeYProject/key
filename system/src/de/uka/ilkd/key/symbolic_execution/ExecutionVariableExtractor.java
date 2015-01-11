package de.uka.ilkd.key.symbolic_execution;

import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionValue;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.model.impl.AbstractExecutionValue;
import de.uka.ilkd.key.symbolic_execution.model.impl.AbstractExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.util.Pair;

/**
 * Extracts the current state and represents it as {@link IExecutionVariable}s.
 * @author Martin Hentschel
 */
public class ExecutionVariableExtractor extends AbstractUpdateExtractor {
   /**
    * The current {@link IExecutionNode}.
    */
   private final IExecutionNode<?> executionNode;
   
   /**
    * An optional additional condition.
    */
   private final Term additionalCondition;
   
   /**
    * The layout term.
    */
   private final Term layoutTerm;
   
   /**
    * The current locations.
    */
   private final Set<ExtractLocationParameter> currentLocations;
   
   /**
    * The objects to ignore.
    */
   private final Set<Term> objectsToIgnore;
   
   /**
    * The found {@link IExecutionVariable}s available via {@link #analyse()}.
    */
   private final Map<LocationDefinition, StateExecutionVariable> allStateVariables;
   
   /**
    * Constructor.
    * @param node The {@link Node} which provides the state.
    * @param modalityPio The {@link PosInOccurrence} in the {@link Node}.
    * @param executionNode The current {@link IExecutionNode}.
    * @param condition An optional additional condition.
    * @throws ProofInputException Occurred Exception
    */
   public ExecutionVariableExtractor(Node node, PosInOccurrence modalityPio, IExecutionNode<?> executionNode, Term condition) throws ProofInputException {
      super(node, modalityPio);
      this.executionNode = executionNode;
      this.additionalCondition = condition;
      // Get path condition
      Term pathCondition = SymbolicExecutionUtil.computePathCondition(executionNode.getProofNode(), false);
      pathCondition = removeImplicitSubTermsFromPathCondition(pathCondition);
      // Extract locations from updates
      Set<ExtractLocationParameter> temporaryCurrentLocations = new LinkedHashSet<ExtractLocationParameter>();
      objectsToIgnore = computeInitialObjectsToIgnore(); // Contains all objects which should be ignored, like exc of the proof obligation and created objects during symbolic execution
      Set<Term> updateCreatedObjects = new LinkedHashSet<Term>(); // Contains all objects which are created during symbolic execution
      Set<Term> updateValueObjects = new LinkedHashSet<Term>(); // Contains all objects which are the value of an update
      collectLocationsFromUpdates(node.sequent(), temporaryCurrentLocations, updateCreatedObjects, updateValueObjects, objectsToIgnore);
      objectsToIgnore.addAll(updateCreatedObjects);
      Set<ExtractLocationParameter> initialLocations = extractLocationsFromTerm(pathCondition, objectsToIgnore);
      initialLocations.addAll(extractLocationsFromSequent(node.sequent(), objectsToIgnore));
      currentLocations = new LinkedHashSet<ExtractLocationParameter>(initialLocations);
      currentLocations.addAll(temporaryCurrentLocations);
      // Create location predicate
      layoutTerm = createLocationPredicateAndTerm(currentLocations);
      // Create state variables
      this.allStateVariables = new LinkedHashMap<LocationDefinition, StateExecutionVariable>();
      for (ExtractLocationParameter location : currentLocations) {
         if (location.isStateMember()) {
            LocationDefinition locDef = new LocationDefinition(location.getProgramVariable(), location.getArrayIndex());
            if (!allStateVariables.containsKey(locDef)) {
               StateExecutionVariable variable = new StateExecutionVariable(executionNode, 
                                                                            node, 
                                                                            modalityPio, 
                                                                            location.getProgramVariable(), 
                                                                            location.getArrayIndex(), 
                                                                            additionalCondition);
               allStateVariables.put(locDef, variable);
            }
         }
      }
   }
   
   /**
    * Extracts the current state and represents it as {@link IExecutionVariable}s.
    * @return The {@link IExecutionVariable}s representing the current state.
    * @throws ProofInputException Occurred Exception.
    */
   public IExecutionVariable[] analyse() throws ProofInputException {
      Collection<StateExecutionVariable> variables = allStateVariables.values();
      return variables.toArray(new StateExecutionVariable[variables.size()]);
   }
   
   /**
    * Analyzes the tree structure of the given {@link ExecutionVariableValuePair}s.
    * @param pairs The {@link ExecutionVariableValuePair}s to analyze.
    * @param topVariables The state locations,
    * @param contentMap The child locations.
    */
   protected void analyzeTreeStructure(Set<ExecutionVariableValuePair> pairs, 
                                       Map<LocationDefinition, List<ExecutionVariableValuePair>> topVariables, 
                                       Map<ParentDefinition, Map<LocationDefinition, List<ExecutionVariableValuePair>>> contentMap) {
      for (ExecutionVariableValuePair pair : pairs) {
         if (pair.isStateMember()) {
            LocationDefinition locDef = new LocationDefinition(pair.getProgramVariable(), pair.getArrayIndex());
            List<ExecutionVariableValuePair> currentTopPairs = topVariables.get(locDef);
            if (currentTopPairs == null) {
               currentTopPairs = new LinkedList<ExecutionVariableValuePair>();
               topVariables.put(locDef, currentTopPairs);
            }
            currentTopPairs.add(pair);
         }
         else {
            ParentDefinition parentDef = new ParentDefinition(pair.getParent(), pair.getGoalNode());
            Map<LocationDefinition, List<ExecutionVariableValuePair>> content = contentMap.get(parentDef);
            if (content == null) {
               content = new LinkedHashMap<LocationDefinition, List<ExecutionVariableValuePair>>();
               contentMap.put(parentDef, content);
            }
            LocationDefinition locDef = new LocationDefinition(pair.getProgramVariable(), pair.getArrayIndex());
            List<ExecutionVariableValuePair> locationContent = content.get(locDef);
            if (locationContent == null) {
               locationContent = new LinkedList<ExecutionVariableValuePair>();
               content.put(locDef, locationContent);
            }
            locationContent.add(pair);
         }
      }
   }
   
   /**
    * Creates an {@link IExecutionVariable} for the given {@link ExecutionVariableValuePair}s.
    * @param pairs The {@link ExecutionVariableValuePair}s to represent.
    * @param contentMap The {@link Map} providing child content information.
    * @param parentValue The optional parent {@link IExecutionValue}.
    * @param alreadyVisitedObjects The value {@link Term}s of already visited objects on the current path in the variable-value-hierarchy.
    * @return The created {@link IExecutionVariable}.
    * @throws ProofInputException Occurred Exception.
    */
   protected IExecutionVariable createVariablesValueStructure(final List<ExecutionVariableValuePair> pairs, 
                                                              final Map<ParentDefinition, Map<LocationDefinition, List<ExecutionVariableValuePair>>> contentMap,
                                                              final ExtractedExecutionValue parentValue,
                                                              final ImmutableList<Term> alreadyVisitedObjects) throws ProofInputException {
      assert !pairs.isEmpty();
      // Create variable
      ExecutionVariableValuePair firstPair = pairs.get(0);
      ExtractedExecutionVariable variable = new ExtractedExecutionVariable(executionNode, 
                                                                           node, 
                                                                           modalityPio, 
                                                                           firstPair.getProgramVariable(), 
                                                                           firstPair.getArrayIndex(), 
                                                                           additionalCondition, 
                                                                           parentValue);
      if (parentValue != null) {
         parentValue.addChildVariable(variable);
      }
      // Fill variable with values
      List<IExecutionValue> values = new LinkedList<IExecutionValue>();
      createValues(variable, pairs, firstPair, contentMap, values, alreadyVisitedObjects);
      variable.setValues(values);
      return variable;
   }
   
   /**
    * Creates the {@link IExecutionValue}s of the given {@link IExecutionVariable}.
    * @param variable The {@link IExecutionVariable}.
    * @param pairs The {@link ExecutionVariableValuePair}s which provides the content.
    * @param firstPair The first entry in the {@link ExecutionVariableValuePair}s.
    * @param contentMap The content {@link Map}.
    * @param valueListToFill The result {@link List} to fill.
    * @param alreadyVisitedObjects The value {@link Term}s of already visited objects on the current path in the variable-value-hierarchy.
    * @throws ProofInputException Occurred Exception.
    */
   protected void createValues(final IExecutionVariable variable, 
                               final List<ExecutionVariableValuePair> pairs, 
                               final ExecutionVariableValuePair firstPair, 
                               final Map<ParentDefinition, Map<LocationDefinition, List<ExecutionVariableValuePair>>> contentMap,
                               final List<IExecutionValue> valueListToFill,
                               final ImmutableList<Term> alreadyVisitedObjects) throws ProofInputException {
      // Group pairs with same value but with different conditions
      Map<Term, List<ExecutionVariableValuePair>> groupedPairs = new LinkedHashMap<Term, List<ExecutionVariableValuePair>>();
      for (ExecutionVariableValuePair pair : pairs) {
         assert firstPair.getProgramVariable() == pair.getProgramVariable();
         assert firstPair.getArrayIndex() == pair.getArrayIndex();
         assert firstPair.isArrayIndex() == pair.isArrayIndex();
         List<ExecutionVariableValuePair> values = groupedPairs.get(pair.getValue());
         if (values == null) {
            values = new LinkedList<ExecutionVariableValuePair>();
            groupedPairs.put(pair.getValue(), values);
         }
         values.add(pair);
      }
      // Create variable
      for (List<ExecutionVariableValuePair> group : groupedPairs.values()) {
         if (group.size() == 1) {
            ExecutionVariableValuePair pair = group.get(0);
            ExtractedExecutionValue value = new ExtractedExecutionValue(executionNode, 
                                                                        node, 
                                                                        variable, 
                                                                        pair.getCondition(), 
                                                                        pair.getValue());
            valueListToFill.add(value);
            Pair<Boolean, ImmutableList<Term>> cycleCheckResult = updateAlreadyVisitedObjects(alreadyVisitedObjects, pair.getValue());
            if (!cycleCheckResult.first) { // No cycle detected
               ParentDefinition parentDef = new ParentDefinition(pair.getValue(), pair.getGoalNode());
               Map<LocationDefinition, List<ExecutionVariableValuePair>> content = contentMap.get(parentDef);
               if (content != null) {
                  for (List<ExecutionVariableValuePair> child : content.values()) {
                     createVariablesValueStructure(child, contentMap, value, cycleCheckResult.second);
                  }
               }
            }
         }
         else {
            List<Term> conditions = new LinkedList<Term>();
            Map<LocationDefinition, List<ExecutionVariableValuePair>> childContentMap = new LinkedHashMap<ExecutionVariableExtractor.LocationDefinition, List<ExecutionVariableValuePair>>();
            for (ExecutionVariableValuePair pair : group) {
               conditions.add(pair.getCondition());
               ParentDefinition parentDef = new ParentDefinition(pair.getValue(), pair.getGoalNode());
               Map<LocationDefinition, List<ExecutionVariableValuePair>> content = contentMap.get(parentDef);
               if (content != null) {
                  for (Entry<LocationDefinition, List<ExecutionVariableValuePair>> entry : content.entrySet()) {
                     List<ExecutionVariableValuePair> childList = childContentMap.get(entry.getKey());
                     if (childList == null) {
                        childList = new LinkedList<ExecutionVariableValuePair>();
                        childContentMap.put(entry.getKey(), childList);
                     }
                     childList.addAll(entry.getValue());
                  }
               }
            }
            Term comboundPathCondition = getServices().getTermBuilder().or(conditions);
            comboundPathCondition = SymbolicExecutionUtil.simplify(getProof(), comboundPathCondition);
            comboundPathCondition = SymbolicExecutionUtil.improveReadability(comboundPathCondition, getServices());
            ExtractedExecutionValue value = new ExtractedExecutionValue(executionNode, 
                                                                        node, 
                                                                        variable, 
                                                                        comboundPathCondition, 
                                                                        group.get(0).getValue());
            valueListToFill.add(value);
            Pair<Boolean, ImmutableList<Term>> cycleCheckResult = updateAlreadyVisitedObjects(alreadyVisitedObjects, group.get(0).getValue());
            if (!cycleCheckResult.first) { // No cycle detected
               if (!childContentMap.isEmpty()) {
                  for (List<ExecutionVariableValuePair> child : childContentMap.values()) {
                     createVariablesValueStructure(child, contentMap, value, cycleCheckResult.second);
                  }
               }
            }
         }
      }
   }
   
   /**
    * Updates the already visited objects list if required.
    * @param alreadyVisitedObjects The value {@link Term}s of already visited objects on the current path in the variable-value-hierarchy.
    * @param value The current value.
    * @return The new already visited objects list or the original one if the current value is not an object.
    */
   protected Pair<Boolean, ImmutableList<Term>> updateAlreadyVisitedObjects(final ImmutableList<Term> alreadyVisitedObjects, Term value) {
      ImmutableList<Term> alreadyVisitedObjectsForChildren = alreadyVisitedObjects;
      boolean cycleDetected = false;
      if (value != null &&
          SymbolicExecutionUtil.hasReferenceSort(getServices(), value) &&
          !SymbolicExecutionUtil.isNullSort(value.sort(), getServices())) {
         if (!alreadyVisitedObjects.contains(value)) {
            alreadyVisitedObjectsForChildren = alreadyVisitedObjectsForChildren.prepend(value);
         }
         else {
            cycleDetected = true;
         }
      }
      return new Pair<Boolean, ImmutableList<Term>>(cycleDetected, alreadyVisitedObjectsForChildren);
   }
   
   /**
    * Utility class representing a parent definition.
    * @author Martin Hentschel
    */
   private static final class ParentDefinition {
      /**
       * The parent.
       */
      private final Term parent;
      
      /**
       * The {@link Node} on which this result is based on.
       */
      private final Node goalNode;

      /**
       * Constructor.
       * @param parent The parent.
       * @param goalNode The {@link Node} on which this result is based on.
       */
      public ParentDefinition(Term parent, Node goalNode) {
         this.parent = parent;
         this.goalNode = goalNode;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean equals(Object obj) {
         if (obj instanceof ParentDefinition) {
            ParentDefinition other = (ParentDefinition)obj;
            return JavaUtil.equals(parent, other.parent) &&
                   JavaUtil.equals(goalNode, other.goalNode);
         }
         else {
            return false;
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public int hashCode() {
         int result = 17;
         result = 31 * result + (parent != null ? parent.hashCode() : 0);
         result = 31 * result + (goalNode != null ? goalNode.hashCode() : 0);
         return result;
      }
   }
   
   /**
    * Utility class representing a location.
    * @author Martin Hentschel
    */
   private static final class LocationDefinition {
      /**
       * The {@link ProgramVariable} or {@code null} if an array index is used instead.
       */
      private final ProgramVariable programVariable;

      /**
       * The array index or {@code null} if a {@link ProgramVariable} is used instead.
       */
      private final Term arrayIndex;

      /**
       * Constructor.
       * @param programVariable The {@link ProgramVariable} or {@code null} if an array index is used instead.
       * @param arrayIndex The array index or {@code null} if a {@link ProgramVariable} is used instead.
       */
      public LocationDefinition(ProgramVariable programVariable, Term arrayIndex) {
         this.programVariable = programVariable;
         this.arrayIndex = arrayIndex;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean equals(Object obj) {
         if (obj instanceof LocationDefinition) {
            LocationDefinition other = (LocationDefinition)obj;
            return programVariable == other.programVariable &&
                   JavaUtil.equals(arrayIndex, other.arrayIndex);
         }
         else {
            return false;
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public int hashCode() {
         int result = 17;
         result = 31 * result + (programVariable != null ? programVariable.hashCode() : 0);
         result = 31 * result + (arrayIndex != null ? arrayIndex.hashCode() : 0);
         return result;
      }
   }
   
   /**
    * The {@link IExecutionVariable} instantiated by the {@link ExecutionVariableExtractor}.
    * @author Martin Hentschel
    */
   private class StateExecutionVariable extends AbstractExecutionVariable {
      /**
       * The contained {@link IExecutionValue}s.
       */
      private IExecutionValue[] values;
      
      /**
       * Constructor.
       * @param parentNode The {@link IExecutionNode} providing relevant information.
       * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
       * @param modalityPIO The {@link PosInOccurrence} of the modality of interest.
       * @param programVariable The represented {@link IProgramVariable} which value is shown.
       * @param arrayIndex The index in the parent array.
       * @param additionalCondition An optional additional condition to consider.
       */
      public StateExecutionVariable(IExecutionNode<?> parentNode, 
                                    Node proofNode, 
                                    PosInOccurrence modalityPIO,
                                    IProgramVariable programVariable,
                                    Term arrayIndex,
                                    Term additionalCondition) {
         super(parentNode.getSettings(), 
               parentNode.getMediator(), 
               proofNode, 
               programVariable, 
               null, 
               arrayIndex, 
               additionalCondition, 
               modalityPIO);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public IExecutionValue[] getValues() throws ProofInputException {
         if (values == null) {
            synchronized (allStateVariables) {
               if (values == null) {
                  // Compute values
                  Set<ExecutionVariableValuePair> pairs = computeVariableValuePairs(getAdditionalCondition(), layoutTerm, currentLocations, true);
                  // Analyze tree structure of pairs
                  Map<LocationDefinition, List<ExecutionVariableValuePair>> topVariables = new LinkedHashMap<LocationDefinition, List<ExecutionVariableValuePair>>();
                  Map<ParentDefinition, Map<LocationDefinition, List<ExecutionVariableValuePair>>> contentMap = new LinkedHashMap<ParentDefinition, Map<LocationDefinition, List<ExecutionVariableValuePair>>>();
                  analyzeTreeStructure(pairs, topVariables, contentMap);
                  // Create variables and values from tree structure
                  for (List<ExecutionVariableValuePair> pairsList : topVariables.values()) {
                     ExecutionVariableValuePair firstPair = pairsList.get(0);
                     List<IExecutionValue> values = new LinkedList<IExecutionValue>();
                     StateExecutionVariable variable = allStateVariables.get(new LocationDefinition(firstPair.getProgramVariable(), firstPair.getArrayIndex()));
                     assert variable != null;
                     createValues(variable, pairsList, firstPair, contentMap, values, ImmutableSLList.<Term>nil());
                     variable.values = values.toArray(new IExecutionValue[values.size()]);
                  }
               }
            }
         }
         return values;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Term createSelectTerm() {
         return SymbolicExecutionUtil.createSelectTerm(this);
      }
   }
   
   /**
    * The {@link IExecutionVariable} instantiated by the {@link ExecutionVariableExtractor}.
    * @author Martin Hentschel
    */
   private static class ExtractedExecutionVariable extends AbstractExecutionVariable {
      /**
       * The contained {@link IExecutionValue}s.
       */
      private List<IExecutionValue> values;
      
      /**
       * Constructor.
       * @param parentNode The {@link IExecutionNode} providing relevant information.
       * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
       * @param modalityPIO The {@link PosInOccurrence} of the modality of interest.
       * @param programVariable The represented {@link IProgramVariable} which value is shown.
       * @param arrayIndex The index in the parent array.
       * @param additionalCondition An optional additional condition to consider.
       * @param parentValue The parent {@link IExecutionValue} or {@code null} if not available.
       */
      public ExtractedExecutionVariable(IExecutionNode<?> parentNode, 
                                        Node proofNode, 
                                        PosInOccurrence modalityPIO,
                                        IProgramVariable programVariable,
                                        Term arrayIndex,
                                        Term additionalCondition,
                                        ExtractedExecutionValue parentValue) {
         super(parentNode.getSettings(), 
               parentNode.getMediator(), 
               proofNode, 
               programVariable, 
               parentValue, 
               arrayIndex, 
               additionalCondition, 
               modalityPIO);
      }
      
      /**
       * Sets the {@link IExecutionValue}s.
       * @param values The {@link IExecutionValue}s to set.
       */
      private void setValues(List<IExecutionValue> values) {
         this.values = values;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public IExecutionValue[] getValues() throws ProofInputException {
         return values.toArray(new IExecutionValue[values.size()]);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Term createSelectTerm() {
         return SymbolicExecutionUtil.createSelectTerm(this);
      }
   }
   
   /**
    * The {@link IExecutionValue} instantiated by the {@link ExecutionVariableExtractor}.
    * @author Martin Hentschel
    */
   private static class ExtractedExecutionValue extends AbstractExecutionValue {
      /**
       * The available child {@link ExtractedExecutionVariable}.
       */
      private final List<ExtractedExecutionVariable> childVariables = new LinkedList<ExtractedExecutionVariable>();

      /**
       * The {@link IExecutionNode} providing the {@link IExecutionConstraint}s.
       */
      private final IExecutionNode<?> parentNode;
      
      /**
       * Constructor.
       * @param parentNode The {@link IExecutionNode} providing relevant information.
       * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
       * @param variable The parent {@link IExecutionVariable} which contains this value.
       * @param condition The condition.
       * @param value The value.
       */
      public ExtractedExecutionValue(IExecutionNode<?> parentNode, 
                                     Node proofNode, 
                                     IExecutionVariable variable, 
                                     Term condition, 
                                     Term value) {
         super(parentNode.getSettings(), parentNode.getMediator(), proofNode, variable, condition, value);
         this.parentNode = parentNode;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getConditionString() throws ProofInputException {
         return getCondition() != null ? formatTerm(getCondition(), getServices()) : null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean isValueUnknown() throws ProofInputException {
         return false;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getValueString() throws ProofInputException {
         return getValue() != null ? formatTerm(getValue(), getServices()) : null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getTypeString() throws ProofInputException {
         return getValue() != null && getValue().sort() != null ? getValue().sort().toString() : null;
      }

      /**
       * Adds a child {@link ExtractedExecutionVariable}.
       * @param variable The {@link ExtractedExecutionVariable} to add.
       */
      protected void addChildVariable(ExtractedExecutionVariable variable) {
         if (variable != null) {
            childVariables.add(variable);
         }
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public ExtractedExecutionVariable[] getChildVariables() throws ProofInputException {
         return childVariables.toArray(new ExtractedExecutionVariable[childVariables.size()]);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      protected IExecutionConstraint[] getNodeConstraints() {
         return parentNode.getConstraints();
      }
   }
}
