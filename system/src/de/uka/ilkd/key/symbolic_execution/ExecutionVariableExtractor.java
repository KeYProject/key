package de.uka.ilkd.key.symbolic_execution;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

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
    * Constructor.
    * @param node The {@link Node} which provides the state.
    * @param modalityPio The {@link PosInOccurrence} in the {@link Node}.
    * @param executionNode The current {@link IExecutionNode}.
    * @param condition An optional additional condition.
    */
   public ExecutionVariableExtractor(Node node, PosInOccurrence modalityPio, IExecutionNode<?> executionNode, Term condition) {
      super(node, modalityPio);
      this.executionNode = executionNode;
      this.additionalCondition = condition;
   }
   
   /**
    * Extracts the current state and represents it as {@link IExecutionVariable}s.
    * @return The {@link IExecutionVariable}s representing the current state.
    * @throws ProofInputException Occurred Exception.
    */
   public IExecutionVariable[] analyse() throws ProofInputException {
      // Get path condition
      Term pathCondition = SymbolicExecutionUtil.computePathCondition(executionNode.getProofNode(), false);
      pathCondition = removeImplicitSubTermsFromPathCondition(pathCondition);
      // Extract locations from updates
      Set<ExtractLocationParameter> temporaryCurrentLocations = new LinkedHashSet<ExtractLocationParameter>();
      Set<Term> objectsToIgnore = computeInitialObjectsToIgnore(); // Contains all objects which should be ignored, like exc of the proof obligation and created objects during symbolic execution
      Set<Term> updateCreatedObjects = new LinkedHashSet<Term>(); // Contains all objects which are created during symbolic execution
      Set<Term> updateValueObjects = new LinkedHashSet<Term>(); // Contains all objects which are the value of an update
      collectLocationsFromUpdates(node.sequent(), temporaryCurrentLocations, updateCreatedObjects, updateValueObjects, objectsToIgnore);
      objectsToIgnore.addAll(updateCreatedObjects);
      Set<ExtractLocationParameter> initialLocations = extractLocationsFromTerm(pathCondition, objectsToIgnore);
      initialLocations.addAll(extractLocationsFromSequent(node.sequent(), objectsToIgnore));
      Set<ExtractLocationParameter> currentLocations = new LinkedHashSet<ExtractLocationParameter>(initialLocations);
      currentLocations.addAll(temporaryCurrentLocations);
      // Create location predicate
      Term layoutTerm = createLocationPredicateAndTerm(currentLocations);
      // Compute values
      if (additionalCondition != null) {
         pathCondition = getServices().getTermBuilder().and(pathCondition, pathCondition);
      }
      Set<ExecutionVariableValuePair> pairs = computeVariableValuePairs(pathCondition, layoutTerm, currentLocations, true);
      return createVariables(pairs, objectsToIgnore);
   }

   /**
    * Creates the {@link IExecutionVariable} representations of the given {@link ExecutionVariableValuePair}s.
    * @param pairs The computed {@link ExecutionVariableValuePair}s.
    * @param objectsToIgnore The objects to ignore.
    * @return The created {@link IExecutionVariable}s.
    * @throws ProofInputException Occurred Exception.
    */
   private IExecutionVariable[] createVariables(Set<ExecutionVariableValuePair> pairs, 
                                                Set<Term> objectsToIgnore) throws ProofInputException {
      List<IExecutionVariable> result = new LinkedList<IExecutionVariable>();
      // Analyze tree structure of pairs
      Map<LocationDefinition, List<ExecutionVariableValuePair>> topVariables = new LinkedHashMap<LocationDefinition, List<ExecutionVariableValuePair>>();
      Map<ParentDefinition, Map<LocationDefinition, List<ExecutionVariableValuePair>>> contentMap = new LinkedHashMap<ParentDefinition, Map<LocationDefinition, List<ExecutionVariableValuePair>>>();
      for (ExecutionVariableValuePair pair : pairs) {
         if (pair.isStateMember()) {
            LocationDefinition locDef = new LocationDefinition(pair);
            List<ExecutionVariableValuePair> currentTopPairs = topVariables.get(locDef);
            if (currentTopPairs == null) {
               currentTopPairs = new LinkedList<ExecutionVariableValuePair>();
               topVariables.put(locDef, currentTopPairs);
            }
            currentTopPairs.add(pair);
         }
         else {
            ParentDefinition parentDef = new ParentDefinition(pair.getParent(), pair.getCondition());
            Map<LocationDefinition, List<ExecutionVariableValuePair>> content = contentMap.get(parentDef);
            if (content == null) {
               content = new LinkedHashMap<LocationDefinition, List<ExecutionVariableValuePair>>();
               contentMap.put(parentDef, content);
            }
            LocationDefinition locDef = new LocationDefinition(pair);
            List<ExecutionVariableValuePair> locationContent = content.get(locDef);
            if (locationContent == null) {
               locationContent = new LinkedList<ExecutionVariableValuePair>();
               content.put(locDef, locationContent);
            }
            locationContent.add(pair);
         }
      }
      // Create variables and values from tree structure
      for (List<ExecutionVariableValuePair> pair : topVariables.values()) {
         IExecutionVariable variable = createVariablesValueStructure(pair, contentMap, null);
         result.add(variable);
      }
      return result.toArray(new ExtractedExecutionVariable[result.size()]);
   }
   
   /**
    * Creates an {@link IExecutionVariable} for the given {@link ExecutionVariableValuePair}s.
    * @param pairs The {@link ExecutionVariableValuePair}s to represent.
    * @param contentMap The {@link Map} providing child content information.
    * @param parentValue The optional parent {@link IExecutionValue}.
    * @return The created {@link IExecutionVariable}.
    * @throws ProofInputException Occurred Exception.
    */
   protected IExecutionVariable createVariablesValueStructure(List<ExecutionVariableValuePair> pairs, 
                                                              Map<ParentDefinition, Map<LocationDefinition, List<ExecutionVariableValuePair>>> contentMap,
                                                              ExtractedExecutionValue parentValue) throws ProofInputException {
      assert !pairs.isEmpty();
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
            variable.addValue(value);
            ParentDefinition parentDef = new ParentDefinition(pair.getValue(), pair.getCondition());
            Map<LocationDefinition, List<ExecutionVariableValuePair>> content = contentMap.get(parentDef);
            if (content != null) {
               for (List<ExecutionVariableValuePair> child : content.values()) {
                  createVariablesValueStructure(child, contentMap, value);
               }
            }
         }
         else {
            List<Term> conditions = new LinkedList<Term>();
            Map<LocationDefinition, List<ExecutionVariableValuePair>> childContentMap = new LinkedHashMap<ExecutionVariableExtractor.LocationDefinition, List<ExecutionVariableValuePair>>();
            for (ExecutionVariableValuePair pair : group) {
               conditions.add(pair.getCondition());
               ParentDefinition parentDef = new ParentDefinition(pair.getValue(), pair.getCondition());
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
            variable.addValue(value);
            if (!childContentMap.isEmpty()) {
               for (List<ExecutionVariableValuePair> child : childContentMap.values()) {
                  createVariablesValueStructure(child, contentMap, value);
               }
            }
         }
      }
      return variable;
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
       * The condition.
       */
      private final Term condition;

      /**
       * Constructor.
       * @param parent The parent.
       * @param condition The condition.
       */
      public ParentDefinition(Term parent, Term condition) {
         this.parent = parent;
         this.condition = condition;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean equals(Object obj) {
         if (obj instanceof ParentDefinition) {
            ParentDefinition other = (ParentDefinition)obj;
            return JavaUtil.equals(parent, other.parent) &&
                   JavaUtil.equals(condition, other.condition);
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
         result = 31 * result + (condition != null ? condition.hashCode() : 0);
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
       * The array index or {@code -1} if a {@link ProgramVariable} is used instead.
       */
      private final int arrayIndex;

      /**
       * Constructor.
       * @param pair The {@link ExecutionVariableValuePair} specifying the location to represent.
       */
      public LocationDefinition(ExecutionVariableValuePair pair) {
         this.programVariable = pair.getProgramVariable();
         this.arrayIndex = pair.getArrayIndex();
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean equals(Object obj) {
         if (obj instanceof LocationDefinition) {
            LocationDefinition other = (LocationDefinition)obj;
            return programVariable == other.programVariable &&
                   arrayIndex == other.arrayIndex;
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
         result = 31 * result + arrayIndex;
         return result;
      }
   }
   
   /**
    * The {@link IExecutionVariable} instantiated by the {@link ExecutionVariableExtractor}.
    * @author Martin Hentschel
    */
   private static class ExtractedExecutionVariable extends AbstractExecutionVariable {
      /**
       * The contained {@link ExtractedExecutionValue}s.
       */
      private final List<ExtractedExecutionValue> values = new LinkedList<ExtractedExecutionValue>();
      
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
                                        int arrayIndex,
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
       * Adds an {@link ExtractedExecutionValue}.
       * @param value The {@link ExtractedExecutionValue} to add.
       */
      protected void addValue(ExtractedExecutionValue value) {
         if (value != null) {
            values.add(value);
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public ExtractedExecutionValue[] getValues() throws ProofInputException {
         return values.toArray(new ExtractedExecutionValue[values.size()]);
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
                                     ExtractedExecutionVariable variable, 
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
