/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution;

import java.util.*;

import de.uka.ilkd.key.java.Services;
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
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.util.Pair;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Extracts the current state and represents it as {@link IExecutionVariable}s.
 *
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
     * The found {@link IExecutionVariable}s available via {@link #analyse()}.
     */
    private final Map<LocationDef, StateExecutionVariable> allStateVariables;

    /**
     * {@code true} simplify conditions, {@code false} do not simplify conditions.
     */
    private final boolean simplifyConditions;

    /**
     * Constructor.
     *
     * @param node The {@link Node} which provides the state.
     * @param modalityPio The {@link PosInOccurrence} in the {@link Node}.
     * @param executionNode The current {@link IExecutionNode}.
     * @param condition An optional additional condition.
     * @param simplifyConditions {@code true} simplify conditions, {@code false} do not simplify
     *        conditions.
     * @throws ProofInputException Occurred Exception
     */
    public ExecutionVariableExtractor(Node node, PosInOccurrence modalityPio,
            IExecutionNode<?> executionNode, Term condition, boolean simplifyConditions)
            throws ProofInputException {
        super(node, modalityPio);
        this.executionNode = executionNode;
        this.additionalCondition = condition;
        this.simplifyConditions = simplifyConditions;
        // Path condition needs always to be simplified, because otherwise additional symbolic
        // values might be introduced.
        Term pathCondition =
            SymbolicExecutionUtil.computePathCondition(executionNode.getProofNode(), true, false);
        pathCondition = removeImplicitSubTermsFromPathCondition(pathCondition);
        // Extract locations from updates
        Set<ExtractLocationParameter> temporaryCurrentLocations = new LinkedHashSet<>();
        // Contains all objects which should be ignored, like the global exc
        // variable of the proof obligation.
        Set<Term> objectsToIgnore = computeInitialObjectsToIgnore(false, false);
        // Contains all objects which are created during symbolic execution
        Set<Term> updateCreatedObjects = new LinkedHashSet<>();
        // Contains all objects which are the value of an update
        Set<Term> updateValueObjects = new LinkedHashSet<>();
        collectLocationsFromUpdates(node.sequent(), temporaryCurrentLocations, updateCreatedObjects,
            updateValueObjects, objectsToIgnore);
        objectsToIgnore.addAll(updateCreatedObjects);
        Set<ExtractLocationParameter> initialLocations =
            extractLocationsFromTerm(pathCondition, objectsToIgnore);
        initialLocations.addAll(extractLocationsFromSequent(node.sequent(), objectsToIgnore));
        currentLocations = new LinkedHashSet<>(initialLocations);
        currentLocations.addAll(temporaryCurrentLocations);
        // Create location predicate
        layoutTerm = createLocationPredicateAndTerm(currentLocations);
        // Create state variables
        this.allStateVariables = new LinkedHashMap<>();
        for (ExtractLocationParameter location : currentLocations) {
            if (location.isStateMember()) {
                LocationDef locDef =
                    new LocationDef(location.getProgramVariable(), location.getArrayIndex());
                if (!allStateVariables.containsKey(locDef)) {
                    StateExecutionVariable variable = new StateExecutionVariable(executionNode,
                        node, modalityPio, location.getProgramVariable(), location.getArrayIndex(),
                        additionalCondition);
                    allStateVariables.put(locDef, variable);
                }
            }
        }
    }

    /**
     * Extracts the current state and represents it as {@link IExecutionVariable}s.
     *
     * @return The {@link IExecutionVariable}s representing the current state.
     * @throws ProofInputException Occurred Exception.
     */
    public IExecutionVariable[] analyse() throws ProofInputException {
        Collection<StateExecutionVariable> variables = allStateVariables.values();
        return variables.toArray(new StateExecutionVariable[0]);
    }

    /**
     * Analyzes the tree structure of the given {@link ExecutionVariableValuePair}s.
     *
     * @param pairs The {@link ExecutionVariableValuePair}s to analyze.
     * @param topVariables The state locations,
     * @param childrenInfo the child locations.
     */
    protected void analyzeTreeStructure(Set<ExecutionVariableValuePair> pairs,
            Map<LocationDef, List<ExecutionVariableValuePair>> topVariables,
            Map<ParentDef, Map<LocationDef, List<ExecutionVariableValuePair>>> childrenInfo) {
        for (ExecutionVariableValuePair pair : pairs) {
            if (pair.isStateMember()) {
                LocationDef locDef =
                    new LocationDef(pair.getProgramVariable(), pair.getArrayIndex());
                List<ExecutionVariableValuePair> currentTopPairs =
                    topVariables.computeIfAbsent(locDef, k -> new LinkedList<>());
                currentTopPairs.add(pair);
            } else {
                ParentDef parentDef =
                    new ParentDef(pair.getParent(), pair.getGoalNode());
                Map<LocationDef, List<ExecutionVariableValuePair>> content =
                    childrenInfo.computeIfAbsent(parentDef, k -> new LinkedHashMap<>());
                LocationDef locDef =
                    new LocationDef(pair.getProgramVariable(), pair.getArrayIndex());
                List<ExecutionVariableValuePair> locationContent =
                    content.computeIfAbsent(locDef, k -> new LinkedList<>());
                locationContent.add(pair);
            }
        }
    }

    /**
     * Creates an {@link IExecutionVariable} for the given {@link ExecutionVariableValuePair}s.
     *
     * @param pairs The {@link ExecutionVariableValuePair}s to represent.
     * @param childrenInfo The {@link Map} providing child content information.
     * @param parentValue The optional parent {@link IExecutionValue}.
     * @param alreadyVisitedObjects The value {@link Term}s of already visited objects on the
     *        current path in the variable-value-hierarchy.
     * @return The created {@link IExecutionVariable}.
     * @throws ProofInputException Occurred Exception.
     */
    protected IExecutionVariable createVariablesValueStructure(
            List<ExecutionVariableValuePair> pairs,
            Map<ParentDef, Map<LocationDef, List<ExecutionVariableValuePair>>> childrenInfo,
            ExtractedExecutionValue parentValue,
            ImmutableList<Term> alreadyVisitedObjects) throws ProofInputException {
        assert !pairs.isEmpty();
        // Create variable
        ExecutionVariableValuePair firstPair = pairs.get(0);
        ExtractedExecutionVariable variable = new ExtractedExecutionVariable(executionNode, node,
            modalityPio, firstPair.getProgramVariable(), firstPair.getArrayIndex(),
            firstPair.getArrayStartIndex(), firstPair.getArrayEndIndex(), additionalCondition,
            parentValue);
        if (parentValue != null) {
            parentValue.addChildVariable(variable);
        }
        // Fill variable with values
        List<IExecutionValue> values = new LinkedList<>();
        createValues(variable, pairs, firstPair, childrenInfo, values, alreadyVisitedObjects);
        variable.setValues(values);
        return variable;
    }

    /**
     * Creates the {@link IExecutionValue}s of the given {@link IExecutionVariable}.
     *
     * @param variable The {@link IExecutionVariable}.
     * @param pairs The {@link ExecutionVariableValuePair}s which provides the content.
     * @param firstPair The first entry in the {@link ExecutionVariableValuePair}s.
     * @param contentMap The content {@link Map}.
     * @param valueListToFill The result {@link List} to fill.
     * @param alreadyVisitedObjects The value {@link Term}s of already visited objects on the
     *        current path in the variable-value-hierarchy.
     * @throws ProofInputException Occurred Exception.
     */
    protected void createValues(final IExecutionVariable variable,
            final List<ExecutionVariableValuePair> pairs,
            final ExecutionVariableValuePair firstPair,
            final Map<ParentDef, Map<LocationDef, List<ExecutionVariableValuePair>>> contentMap,
            final List<IExecutionValue> valueListToFill,
            final ImmutableList<Term> alreadyVisitedObjects) throws ProofInputException {
        // Group pairs with same value but with different conditions
        Map<Term, List<ExecutionVariableValuePair>> groupedPairs =
            new LinkedHashMap<>();
        for (ExecutionVariableValuePair pair : pairs) {
            assert firstPair.getProgramVariable() == pair.getProgramVariable();
            assert firstPair.getArrayIndex() == pair.getArrayIndex();
            assert firstPair.isArrayIndex() == pair.isArrayIndex();
            assert firstPair.getArrayStartIndex() == pair.getArrayStartIndex();
            assert firstPair.getArrayEndIndex() == pair.getArrayEndIndex();
            assert firstPair.isArrayRange() == pair.isArrayRange();
            List<ExecutionVariableValuePair> values =
                groupedPairs.computeIfAbsent(pair.getValue(), k -> new LinkedList<>());
            values.add(pair);
        }
        // Create variable
        for (List<ExecutionVariableValuePair> group : groupedPairs.values()) {
            if (group.size() == 1) {
                ExecutionVariableValuePair pair = group.get(0);
                ExtractedExecutionValue value = new ExtractedExecutionValue(executionNode, node,
                    variable, pair.getCondition(), pair.getValue());
                valueListToFill.add(value);
                Pair<Boolean, ImmutableList<Term>> cycleCheckResult =
                    updateAlreadyVisitedObjects(alreadyVisitedObjects, pair.getValue());
                if (!cycleCheckResult.first) { // No cycle detected
                    ParentDef parentDef =
                        new ParentDef(pair.getValue(), pair.getGoalNode());
                    Map<LocationDef, List<ExecutionVariableValuePair>> content =
                        contentMap.get(parentDef);
                    if (content != null) {
                        for (List<ExecutionVariableValuePair> child : content.values()) {
                            createVariablesValueStructure(child, contentMap, value,
                                cycleCheckResult.second);
                        }
                    }
                }
            } else {
                List<Term> conditions = new LinkedList<>();
                Map<LocationDef, List<ExecutionVariableValuePair>> childContentMap =
                    new LinkedHashMap<>();
                for (ExecutionVariableValuePair pair : group) {
                    conditions.add(pair.getCondition());
                    ParentDef parentDef =
                        new ParentDef(pair.getValue(), pair.getGoalNode());
                    Map<LocationDef, List<ExecutionVariableValuePair>> content =
                        contentMap.get(parentDef);
                    if (content != null) {
                        for (var entry : content.entrySet()) {
                            List<ExecutionVariableValuePair> childList =
                                childContentMap.computeIfAbsent(entry.getKey(),
                                    k -> new LinkedList<>());
                            childList.addAll(entry.getValue());
                        }
                    }
                }
                final Services services = getServices();
                Term compoundPathCondition = services.getTermBuilder().or(conditions);
                if (simplifyConditions) {
                    compoundPathCondition = SymbolicExecutionUtil.simplify(
                        getProof().getInitConfig(), getProof(), compoundPathCondition);
                }
                compoundPathCondition =
                    SymbolicExecutionUtil.improveReadability(compoundPathCondition, services);
                ExtractedExecutionValue value = new ExtractedExecutionValue(executionNode, node,
                    variable, compoundPathCondition, group.get(0).getValue());
                valueListToFill.add(value);
                Pair<Boolean, ImmutableList<Term>> cycleCheckResult =
                    updateAlreadyVisitedObjects(alreadyVisitedObjects, group.get(0).getValue());
                if (!cycleCheckResult.first) { // No cycle detected
                    if (!childContentMap.isEmpty()) {
                        for (List<ExecutionVariableValuePair> child : childContentMap.values()) {
                            createVariablesValueStructure(child, contentMap, value,
                                cycleCheckResult.second);
                        }
                    }
                }
            }
        }
    }

    /**
     * Updates the already visited objects list if required.
     *
     * @param alreadyVisitedObjects The value {@link Term}s of already visited objects on the
     *        current path in the variable-value-hierarchy.
     * @param value The current value.
     * @return The new already visited objects list or the original one if the current value is not
     *         an object.
     */
    protected Pair<Boolean, ImmutableList<Term>> updateAlreadyVisitedObjects(
            final ImmutableList<Term> alreadyVisitedObjects, Term value) {
        ImmutableList<Term> alreadyVisitedObjectsForChildren = alreadyVisitedObjects;
        boolean cycleDetected = false;
        if (value != null && SymbolicExecutionUtil.hasReferenceSort(getServices(), value)
                && !SymbolicExecutionUtil.isNullSort(value.sort(), getServices())) {
            if (!alreadyVisitedObjects.contains(value)) {
                alreadyVisitedObjectsForChildren = alreadyVisitedObjectsForChildren.prepend(value);
            } else {
                cycleDetected = true;
            }
        }
        return new Pair<>(cycleDetected, alreadyVisitedObjectsForChildren);
    }

    /**
     * Utility class representing a parent definition.
     *
     * @author Martin Hentschel
     */
    private static final class ParentDef {
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
         *
         * @param parent The parent.
         * @param goalNode The {@link Node} on which this result is based on.
         */
        public ParentDef(Term parent, Node goalNode) {
            this.parent = parent;
            this.goalNode = goalNode;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public boolean equals(Object obj) {
            if (obj instanceof ParentDef) {
                ParentDef other = (ParentDef) obj;
                return Objects.equals(parent, other.parent)
                        && Objects.equals(goalNode, other.goalNode);
            } else {
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
     *
     * @author Martin Hentschel
     */
    private static final class LocationDef {
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
         *
         * @param programVariable The {@link ProgramVariable} or {@code null} if an array index is
         *        used instead.
         * @param arrayIndex The array index or <code>null</code>, if a {@link ProgramVariable} is
         *        used instead.
         */
        public LocationDef(ProgramVariable programVariable, Term arrayIndex) {
            this.programVariable = programVariable;
            this.arrayIndex = arrayIndex;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public boolean equals(Object obj) {
            if (obj instanceof LocationDef) {
                LocationDef other = (LocationDef) obj;
                return programVariable == other.programVariable
                        && Objects.equals(arrayIndex, other.arrayIndex);
            } else {
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
     *
     * @author Martin Hentschel
     */
    private class StateExecutionVariable extends AbstractExecutionVariable {
        /**
         * The contained {@link IExecutionValue}s.
         */
        private IExecutionValue[] values;

        /**
         * Constructor.
         *
         * @param parentNode The {@link IExecutionNode} providing relevant information.
         * @param proofNode The {@link Node} of KeY's proof tree which is represented by this
         *        {@link IExecutionNode}.
         * @param modalityPIO The {@link PosInOccurrence} of the modality of interest.
         * @param programVariable The represented {@link IProgramVariable} which value is shown.
         * @param arrayIndex The index in the parent array.
         * @param additionalCondition An optional additional condition to consider.
         */
        public StateExecutionVariable(IExecutionNode<?> parentNode, Node proofNode,
                PosInOccurrence modalityPIO, IProgramVariable programVariable, Term arrayIndex,
                Term additionalCondition) {
            super(parentNode.getSettings(), proofNode, programVariable, null, arrayIndex,
                additionalCondition, modalityPIO);
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public synchronized IExecutionValue[] getValues() throws ProofInputException {
            if (values != null) {
                return values;
            }
            // Compute values
            Set<ExecutionVariableValuePair> pairs =
                computeVariableValuePairs(getAdditionalCondition(), layoutTerm,
                    currentLocations, true, simplifyConditions);
            if (pairs == null) {
                // Something went wrong, values are not available.
                return new IExecutionValue[0];
            }
            // Analyze tree structure of pairs
            Map<LocationDef, List<ExecutionVariableValuePair>> topVariables =
                new LinkedHashMap<>();
            Map<ParentDef, Map<LocationDef, List<ExecutionVariableValuePair>>> childrenInfo =
                new LinkedHashMap<>();
            analyzeTreeStructure(pairs, topVariables, childrenInfo);
            // Create variables and values from tree structure
            for (List<ExecutionVariableValuePair> pairsList : topVariables.values()) {
                ExecutionVariableValuePair firstPair = pairsList.get(0);
                List<IExecutionValue> values = new LinkedList<>();
                StateExecutionVariable variable =
                    allStateVariables.get(new LocationDef(
                        firstPair.getProgramVariable(), firstPair.getArrayIndex()));
                assert variable != null;
                createValues(variable, pairsList, firstPair, childrenInfo, values,
                    ImmutableSLList.nil());
                variable.values = values.toArray(new IExecutionValue[0]);
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
     *
     * @author Martin Hentschel
     */
    public static class ExtractedExecutionVariable extends AbstractExecutionVariable {
        /**
         * The contained {@link IExecutionValue}s.
         */
        private List<IExecutionValue> values;

        /**
         * The array start index or {@code null} if not used.
         */
        private final Term arrayStartIndex;

        /**
         * The array end index or {@code null} if not used.
         */
        private final Term arrayEndIndex;

        /**
         * Constructor.
         *
         * @param parentNode The {@link IExecutionNode} providing relevant information.
         * @param proofNode The {@link Node} of KeY's proof tree which is represented by this
         *        {@link IExecutionNode}.
         * @param modalityPIO The {@link PosInOccurrence} of the modality of interest.
         * @param programVariable The represented {@link IProgramVariable} which value is shown.
         * @param arrayIndex The index in the parent array.
         * @param additionalCondition An optional additional condition to consider.
         * @param parentValue The parent {@link IExecutionValue} or {@code null} if not available.
         */
        public ExtractedExecutionVariable(IExecutionNode<?> parentNode, Node proofNode,
                PosInOccurrence modalityPIO, IProgramVariable programVariable, Term arrayIndex,
                Term arrayStartIndex, Term arrayEndIndex, Term additionalCondition,
                ExtractedExecutionValue parentValue) {
            super(parentNode.getSettings(), proofNode, programVariable, parentValue, arrayIndex,
                additionalCondition, modalityPIO);
            this.arrayStartIndex = arrayStartIndex;
            this.arrayEndIndex = arrayEndIndex;
        }

        /**
         * Sets the {@link IExecutionValue}s.
         *
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
            return values.toArray(new IExecutionValue[0]);
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public Term createSelectTerm() {
            return SymbolicExecutionUtil.createSelectTerm(this);
        }

        /**
         * Returns the array start index.
         *
         * @return The array start index.
         */
        public Term getArrayStartIndex() {
            return arrayStartIndex;
        }

        /**
         * Returns the human-readable array start index.
         *
         * @return The human-readable array start index.
         */
        public String getArrayStartIndexString() {
            return arrayStartIndex != null ? formatTerm(arrayStartIndex, getServices()) : null;
        }

        /**
         * Returns the array end index.
         *
         * @return The array end index.
         */
        public Term getArrayEndIndex() {
            return arrayEndIndex;
        }

        /**
         * Returns the human-readable array end index.
         *
         * @return The human-readable array end index.
         */
        public String getArrayEndIndexString() {
            return arrayEndIndex != null ? formatTerm(arrayEndIndex, getServices()) : null;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        protected String lazyComputeName() throws ProofInputException {
            if (getArrayStartIndex() != null || getArrayEndIndex() != null) {
                String name = "[";
                if (getArrayStartIndex() != null) {
                    name += getArrayIndexString() + " >= " + getArrayStartIndexString();
                }
                if (getArrayStartIndex() != null && getArrayEndIndex() != null) {
                    name += " and ";
                }
                if (getArrayEndIndex() != null) {
                    name += getArrayIndexString() + " <= " + getArrayEndIndexString();
                }
                name += "]";
                return name;
            } else {
                return super.lazyComputeName();
            }
        }
    }

    /**
     * The {@link IExecutionValue} instantiated by the {@link ExecutionVariableExtractor}.
     *
     * @author Martin Hentschel
     */
    public static class ExtractedExecutionValue extends AbstractExecutionValue {
        /**
         * The available child {@link ExtractedExecutionVariable}.
         */
        private final List<ExtractedExecutionVariable> childVariables = new LinkedList<>();

        /**
         * The {@link IExecutionNode} providing the {@link IExecutionConstraint}s.
         */
        private final IExecutionNode<?> parentNode;

        /**
         * Constructor.
         *
         * @param parentNode The {@link IExecutionNode} providing relevant information.
         * @param proofNode The {@link Node} of KeY's proof tree which is represented by this
         *        {@link IExecutionNode}.
         * @param variable The parent {@link IExecutionVariable} which contains this value.
         * @param condition The condition.
         * @param value The value.
         */
        public ExtractedExecutionValue(IExecutionNode<?> parentNode, Node proofNode,
                IExecutionVariable variable, Term condition, Term value) {
            super(parentNode.getSettings(), proofNode, variable, condition, value);
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
            return getValue() != null && getValue().sort() != null ? getValue().sort().toString()
                    : null;
        }

        /**
         * Adds a child {@link ExtractedExecutionVariable}.
         *
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
        public ExtractedExecutionVariable[] getChildVariables() {
            return childVariables.toArray(new ExtractedExecutionVariable[0]);
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
