/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution;

import java.util.*;
import java.util.Map.Entry;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionAllArrayIndicesVariable;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicLayout;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionSideProofUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.engine.impl.ApplyStrategyInfo;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.Strings;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.java.CollectionUtil;

/**
 * Provides the basic functionality to extract values from updates.
 *
 * @author Martin Hentschel
 */
public abstract class AbstractUpdateExtractor {
    /**
     * Contains the {@link Node} of KeY's proof tree to compute memory layouts for.
     */
    protected final Node node;

    /**
     * The {@link PosInOccurrence} of the modality or its updates.
     */
    protected final PosInOccurrence modalityPio;

    /**
     * An incremented number used to give each pre value an unique name.
     */
    private int preVariableIndex = 0;

    /**
     * Constructor.
     *
     * @param node The {@link Node} of KeY's proof tree to compute memory layouts for.
     * @param modalityPio The {@link PosInOccurrence} of the modality or its updates.
     */
    protected AbstractUpdateExtractor(Node node,
            PosInOccurrence modalityPio) {
        assert node != null;
        assert modalityPio != null;
        this.node = node;
        this.modalityPio = modalityPio;
    }

    /**
     * Removes all conditions from the given path condition which contains implicit
     * {@link IProgramVariable}s.
     *
     * @param pathCondition The path condition to check.
     * @return The new path condition without conditions which uses implicit
     *         {@link IProgramVariable}s.
     */
    protected JTerm removeImplicitSubTermsFromPathCondition(JTerm pathCondition) {
        if (Junctor.AND == pathCondition.op()) {
            // Path condition with multiple terms combined via AND
            List<JTerm> newTerms = new LinkedList<>();
            for (JTerm sub : pathCondition.subs()) {
                if (!containsImplicitProgramVariable(sub)) {
                    newTerms.add(sub);
                }
            }
            return getServices().getTermBuilder().and(newTerms);
        } else {
            // Only one term in path condition
            if (!containsImplicitProgramVariable(pathCondition)) {
                return pathCondition;
            } else {
                return getServices().getTermBuilder().tt();
            }
        }
    }

    /**
     * Checks if the given {@link JTerm} contains an implicit {@link IProgramVariable}.
     *
     * @param term The {@link JTerm} to check.
     * @return {@code true} {@link JTerm} contains implicit {@link IProgramVariable}, {@code false}
     *         {@link JTerm} contains no implicit {@link IProgramVariable}.
     */
    protected boolean containsImplicitProgramVariable(JTerm term) {
        if (term.op() instanceof ProgramVariable
                && isImplicitProgramVariable((ProgramVariable) term.op())) {
            return true;
        }
        for (int i = 0; i < term.arity(); i++) {
            if (containsImplicitProgramVariable(term.sub(i))) {
                return true;
            }
        }
        return false;
    }

    /**
     * Checks if the given {@link ProgramVariable} is implicit.
     *
     * @param var The {@link ProgramVariable} to check.
     * @return {@code true} {@link ProgramVariable} is implicit, {@code false}
     *         {@link ProgramVariable} is not implicit or {@code null}.
     */
    protected boolean isImplicitProgramVariable(ProgramVariable var) {
        return var != null && var.isImplicit();
    }

    /**
     * <p>
     * Computes objects which should be ignored in the state because they are part of the proof
     * obligation and not of the source code.
     * </p>
     * <p>
     * By default the set will contain the exc variable and the backup of arguments and the heap.
     * </p>
     *
     * @param ignoreExceptionVariable Ignore exception variable?
     * @param ignoreOldStateVariables Ignore old state variables?
     * @return The objects to ignore.
     */
    protected Set<JTerm> computeInitialObjectsToIgnore(boolean ignoreExceptionVariable,
            boolean ignoreOldStateVariables) {
        Set<JTerm> result = new LinkedHashSet<>();
        if (ignoreExceptionVariable) {
            // Add exception variable to the ignore list because it is not part of the source code.
            IProgramVariable excVar = SymbolicExecutionUtil.extractExceptionVariable(getProof());
            if (excVar instanceof ProgramVariable) {
                result.add(getServices().getTermBuilder().var((ProgramVariable) excVar));
            }
        }
        if (ignoreOldStateVariables) {
            // Add initial updates which are used as backup of the heap and method arguments. They
            // are not part of the source code and should be ignored.
            Sequent sequent = getRoot().sequent();
            for (SequentFormula sf : sequent.succedent()) {
                JTerm term = (JTerm) sf.formula();
                if (Junctor.IMP.equals(term.op())) {
                    fillInitialObjectsToIgnoreRecursively(term.sub(1), result);
                }
            }
        }
        return result;
    }

    /**
     * Utility method of {@link #computeInitialObjectsToIgnore} which computes the objects to
     * ignore recursively.
     *
     * @param term The current {@link JTerm}.
     * @param toFill The {@link Set} with {@link JTerm}s to ignore to fill.
     */
    protected void fillInitialObjectsToIgnoreRecursively(JTerm term, Set<JTerm> toFill) {
        if (term.op() instanceof UpdateApplication) {
            JTerm updateTerm = UpdateApplication.getUpdate(term);
            fillInitialObjectsToIgnoreRecursively(updateTerm, toFill);
        } else if (term.op() == UpdateJunctor.PARALLEL_UPDATE) {
            for (int i = 0; i < term.arity(); i++) {
                fillInitialObjectsToIgnoreRecursively(term.sub(i), toFill);
            }
        } else if (term.op() instanceof ElementaryUpdate eu) {
            if (eu.lhs() instanceof ProgramVariable) {
                toFill.add(term.sub(0));
            }
        }
    }

    /**
     * <p>
     * Computes for each location (value/association of an object) used in the updates of the given
     * {@link Sequent} the {@link JTerm}s which allows to compute the object itself and the value of
     * the value/association. The result is a {@link Set} of {@link ExtractLocationParameter} which
     * contains the computed {@link JTerm}s.
     * </p>
     * <p>
     * Objects which are created in the heap during symbolic execution and all objects which are
     * used on the right side of associations are also collected and stored in the {@link Set}s
     * {@code updateCreatedObjectsToFill}/ {@code updateValueObjectsToFill}.
     * </p>
     *
     * @param sequent The {@link Sequent} which provides the updates to extract locations from.
     * @param locationsToFill The location {@link Set} to fill.
     * @param updateCreatedObjectsToFill The new created object {@link Set} to fill.
     * @param updateValueObjectsToFill The {@link Set} with objects used on right side of updates to
     *        fill.
     * @param objectsToIgnore The objects to ignore.
     * @throws ProofInputException Occurred Exception.
     */
    protected void collectLocationsFromUpdates(Sequent sequent,
            Set<ExtractLocationParameter> locationsToFill, Set<JTerm> updateCreatedObjectsToFill,
            Set<JTerm> updateValueObjectsToFill, Set<JTerm> objectsToIgnore)
            throws ProofInputException {
        // Go up in parent hierarchy and collect updates on all update applications
        PosInOccurrence pio = modalityPio;
        while (pio != null) {
            JTerm updateApplication = (JTerm) pio.subTerm();
            if (updateApplication.op() == UpdateApplication.UPDATE_APPLICATION) {
                JTerm topUpdate = UpdateApplication.getUpdate(updateApplication);
                collectLocationsFromTerm(topUpdate, locationsToFill, updateCreatedObjectsToFill,
                    updateValueObjectsToFill, objectsToIgnore);
            }
            if (!pio.isTopLevel()) {
                pio = pio.up();
            } else {
                pio = null;
            }
        }
    }

    /**
     * <p>
     * Computes for each location (value/association of an object) used in the the given
     * {@link JTerm} the {@link JTerm}s which allows to compute the object itself and the value of
     * the
     * value/association. The result is a {@link Set} of {@link ExtractLocationParameter} which
     * contains the computed {@link JTerm}s.
     * </p>
     * <p>
     * Objects which are created in the heap during symbolic execution and all objects which are
     * used on the right side of associations are also collected and stored in the {@link Set}s
     * {@code updateCreatedObjectsToFill}/ {@code updateValueObjectsToFill}.
     * </p>
     *
     * @param updateTerm The {@link JTerm} which provides the update to extract locations from.
     * @param locationsToFill The location {@link Set} to fill.
     * @param updateCreatedObjectsToFill The new created object {@link Set} to fill.
     * @param updateValueObjectsToFill The {@link Set} with objects used on right side of updates to
     *        fill.
     * @param objectsToIgnore The objects to ignore.
     * @throws ProofInputException Occurred Exception.
     */
    protected void collectLocationsFromTerm(JTerm updateTerm,
            Set<ExtractLocationParameter> locationsToFill, Set<JTerm> updateCreatedObjectsToFill,
            Set<JTerm> updateValueObjectsToFill, Set<JTerm> objectsToIgnore)
            throws ProofInputException {
        if (updateTerm.op() instanceof UpdateJunctor) {
            for (JTerm sub : updateTerm.subs()) {
                collectLocationsFromTerm(sub, locationsToFill, updateCreatedObjectsToFill,
                    updateValueObjectsToFill, objectsToIgnore);
            }
        } else if (updateTerm.op() instanceof ElementaryUpdate eu) {
            if (SymbolicExecutionUtil.isHeapUpdate(getServices(), updateTerm)) {
                collectLocationsFromHeapUpdate(updateTerm.sub(0), locationsToFill,
                    updateCreatedObjectsToFill, updateValueObjectsToFill);
            } else if (eu.lhs() instanceof ProgramVariable var) {
                final HeapLDT heapLDT = getServices().getTypeConverter().getHeapLDT();
                if (!SymbolicExecutionUtil.isHeap(var, heapLDT)) {
                    if (!isImplicitProgramVariable(var)
                            && !objectsToIgnore.contains(getServices().getTermBuilder().var(var))
                            && !hasFreeVariables(updateTerm)) {
                        locationsToFill.add(new ExtractLocationParameter(var, true));
                    }
                    if (SymbolicExecutionUtil.hasReferenceSort(getServices(), updateTerm.sub(0))) {
                        JTerm objectTerm = updateTerm.sub(0);
                        objectTerm = SymbolicExecutionUtil.replaceSkolemConstants(node.sequent(),
                            objectTerm, getServices());
                        updateValueObjectsToFill
                                .add(OriginTermLabel.removeOriginLabels(objectTerm, getServices()));
                    }
                }
            } else {
                throw new ProofInputException("Unsupported update operator \"" + eu.lhs() + "\".");
            }
        } else {
            throw new ProofInputException(
                "Unsupported update operator \"" + updateTerm.op() + "\".");
        }
    }

    /**
     * <p>
     * Computes for each location (value/association of an object) used in the the given heap update
     * {@link JTerm} the {@link JTerm}s which allows to compute the object itself and the value of
     * the
     * value/association. The result is a {@link Set} of {@link ExtractLocationParameter} which
     * contains the computed {@link JTerm}s.
     * </p>
     * <p>
     * Objects which are created in the heap during symbolic execution and all objects which are
     * used on the right side of associations are also collected and stored in the {@link Set}s
     * {@code updateCreatedObjectsToFill}/ {@code updateValueObjectsToFill}.
     * </p>
     *
     * @param term The {@link JTerm} which provides the heap update to extract locations from.
     * @param locationsToFill The location {@link Set} to fill.
     * @param updateCreatedObjectsToFill The new created object {@link Set} to fill.
     * @param updateValueObjectsToFill The {@link Set} with objects used on right side of updates to
     *        fill.
     * @throws ProofInputException Occurred Exception.
     */
    protected void collectLocationsFromHeapUpdate(JTerm term,
            Set<ExtractLocationParameter> locationsToFill, Set<JTerm> updateCreatedObjectsToFill,
            Set<JTerm> updateValueObjectsToFill) throws ProofInputException {
        final HeapLDT heapLDT = getServices().getTypeConverter().getHeapLDT();
        if (term.op() == heapLDT.getStore()) {
            // Add select object term to result
            JTerm selectArgument = term.sub(1);
            if (heapLDT.getSortOfSelect(selectArgument.op()) != null) {
                ProgramVariable var = SymbolicExecutionUtil.getProgramVariable(getServices(),
                    heapLDT, selectArgument.sub(2));
                if (var != null) {
                    if (!isImplicitProgramVariable(var)
                            && !hasFreeVariables(selectArgument.sub(2))) {
                        locationsToFill
                                .add(new ExtractLocationParameter(var, selectArgument.sub(1)));
                    }
                } else {
                    JTerm arrayIndex = SymbolicExecutionUtil.getArrayIndex(getServices(), heapLDT,
                        selectArgument.sub(2));
                    if (arrayIndex != null) {
                        if (!hasFreeVariables(arrayIndex)) {
                            locationsToFill.add(
                                new ExtractLocationParameter(arrayIndex, selectArgument.sub(1)));
                        }
                    } else {
                        throw new ProofInputException(
                            "Unsupported select statement \"" + term + "\".");
                    }
                }
            } else if (selectArgument.op() instanceof IProgramVariable) {
                ProgramVariable var = (ProgramVariable) selectArgument.op();
                if (!isImplicitProgramVariable(var) && !hasFreeVariables(selectArgument)) {
                    locationsToFill.add(new ExtractLocationParameter(var, false));
                }
            } else if (heapLDT.getNull() == selectArgument.op()) {
                // Static fields have a null term as select argument.
            } else {
                for (int i = 0; i < selectArgument.arity(); i++) {
                    collectLocationsFromHeapUpdate(selectArgument.sub(i), locationsToFill,
                        updateCreatedObjectsToFill, updateValueObjectsToFill);
                }
            }
            // Add select value term to result
            ProgramVariable var =
                SymbolicExecutionUtil.getProgramVariable(getServices(), heapLDT, term.sub(2));
            if (var != null) {
                if (!isImplicitProgramVariable(var) && !hasFreeVariables(term.sub(2))) {
                    if (var.isStatic()) {
                        locationsToFill.add(new ExtractLocationParameter(var, true));
                    } else {
                        locationsToFill.add(new ExtractLocationParameter(var, term.sub(1)));
                    }
                }
            } else {
                JTerm arrayIndex =
                    SymbolicExecutionUtil.getArrayIndex(getServices(), heapLDT, term.sub(2));
                if (arrayIndex != null && !hasFreeVariables(arrayIndex)) {
                    locationsToFill.add(new ExtractLocationParameter(arrayIndex, term.sub(1)));
                } else {
                    throw new ProofInputException("Unsupported select statement \"" + term + "\".");
                }
            }
            if (SymbolicExecutionUtil.hasReferenceSort(getServices(), term.sub(3))
                    && term.sub(3).op() instanceof ProgramVariable) {
                JTerm objectTerm = term.sub(3);
                objectTerm = SymbolicExecutionUtil.replaceSkolemConstants(node.sequent(),
                    objectTerm, getServices());
                updateValueObjectsToFill
                        .add(OriginTermLabel.removeOriginLabels(objectTerm, getServices()));
            }
            // Iterate over child heap modifications
            collectLocationsFromHeapUpdate(term.sub(0), locationsToFill, updateCreatedObjectsToFill,
                updateValueObjectsToFill);
        } else if (term.op() == heapLDT.getCreate()) {
            JTerm newObject = term.sub(1);
            newObject = SymbolicExecutionUtil.replaceSkolemConstants(node.sequent(), newObject,
                getServices());
            updateCreatedObjectsToFill
                    .add(OriginTermLabel.removeOriginLabels(newObject, getServices()));
            // Iterate over child heap modifications
            collectLocationsFromHeapUpdate(term.sub(0), locationsToFill, updateCreatedObjectsToFill,
                updateValueObjectsToFill);
        } else if (term.op() == heapLDT.getHeap()) {
            // Initial Heap, nothing to do
        } else if (term.op() == heapLDT.getMemset()) {
            // Check modified array range.
            JTerm arrayRange = term.sub(1);
            if (arrayRange.op() == getServices().getTypeConverter().getLocSetLDT()
                    .getArrayRange()) {
                JTerm array = arrayRange.sub(0);
                JTerm startIndex = arrayRange.sub(1);
                JTerm endIndex = arrayRange.sub(2);
                locationsToFill.add(new ExtractLocationParameter(startIndex, endIndex, array));
            }
            // Iterate over child heap modifications
            collectLocationsFromHeapUpdate(term.sub(0), locationsToFill, updateCreatedObjectsToFill,
                updateValueObjectsToFill);
        } else {
            for (int i = 0; i < term.arity(); i++) {
                collectLocationsFromHeapUpdate(term.sub(i), locationsToFill,
                    updateCreatedObjectsToFill, updateValueObjectsToFill);
            }
        }
    }

    /**
     * Checks if the given {@link JTerm} has free variables.
     *
     * @param term The {@link JTerm} to check.
     * @return {@code true} has free variables, {@code false} does not have free variables.
     */
    protected boolean hasFreeVariables(JTerm term) {
        return term != null && !term.freeVars().isEmpty();
    }

    /**
     * Computes for each location (value/association of an object) used in the given {@link Sequent}
     * the {@link JTerm}s which allows to compute the object itself and the value of the
     * value/association. The result is a {@link Set} of {@link ExtractLocationParameter} which
     * contains the computed {@link JTerm}s.
     *
     * @param sequent The {@link Sequent} to extract locations from.
     * @param objectsToIgnore The objects to ignore.
     * @return The found locations.
     * @throws ProofInputException Occurred Exception.
     */
    protected Set<ExtractLocationParameter> extractLocationsFromSequent(Sequent sequent,
            Set<JTerm> objectsToIgnore) throws ProofInputException {
        Set<ExtractLocationParameter> result = new LinkedHashSet<>();
        for (SequentFormula sf : sequent) {
            result.addAll(extractLocationsFromTerm(
                OriginTermLabel.removeOriginLabels((JTerm) sf.formula(), getServices()),
                objectsToIgnore));
        }
        return result;
    }

    /**
     * Computes for each location (value/association of an object) used in the given {@link JTerm}
     * the {@link JTerm}s which allows to compute the object itself and the value of the
     * value/association. The result is a {@link Set} of {@link ExtractLocationParameter} which
     * contains the computed {@link JTerm}s.
     *
     * @param term The {@link JTerm} to extract locations from.
     * @param objectsToIgnore The objects to ignore.
     * @return The found locations.
     * @throws ProofInputException Occurred Exception.
     */
    protected Set<ExtractLocationParameter> extractLocationsFromTerm(JTerm term,
            Set<JTerm> objectsToIgnore) throws ProofInputException {
        Set<ExtractLocationParameter> result = new LinkedHashSet<>();
        collectLocationsFromTerm(result, term, objectsToIgnore);
        return result;
    }

    /**
     * Utility method of {@link #extractLocationsFromTerm(JTerm, Set)} which recursively extracts
     * the
     * locations.
     *
     * @param toFill The result {@link Set} to fill.
     * @param term The current {@link JTerm}.
     * @param objectsToIgnore The objects to ignore.
     * @throws ProofInputException Occurred Exception.
     */
    protected void collectLocationsFromTerm(Set<ExtractLocationParameter> toFill, JTerm term,
            Set<JTerm> objectsToIgnore) throws ProofInputException {
        term = OriginTermLabel.removeOriginLabels(term, getServices());
        final HeapLDT heapLDT = getServices().getTypeConverter().getHeapLDT();
        if (term.op() instanceof ProgramVariable var) {
            if (!SymbolicExecutionUtil.isHeap(var, heapLDT) && !isImplicitProgramVariable(var)
                    && !objectsToIgnore.contains(term) && !hasFreeVariables(term)) {
                toFill.add(new ExtractLocationParameter(var, true));
            }
        } else {
            Sort sort = heapLDT.getSortOfSelect(term.op());
            if (sort != null) {
                collectLocationsFromHeapTerms(term.sub(1), term.sub(2), heapLDT, toFill,
                    objectsToIgnore);
            } else if (heapLDT.getStore() == term.op()) {
                collectLocationsFromHeapTerms(term.sub(1), term.sub(2), heapLDT, toFill,
                    objectsToIgnore);
            } else if (heapLDT.getLength() == term.op()) {
                if (!objectsToIgnore.contains(term.sub(0)) && !hasFreeVariables(term)) {
                    ProgramVariable var = getServices().getJavaInfo().getArrayLength();
                    toFill.add(new ExtractLocationParameter(var, term.sub(0)));
                }
            } else {
                for (JTerm sub : term.subs()) {
                    collectLocationsFromTerm(toFill, sub, objectsToIgnore);
                }
            }
        }
    }

    /**
     * Collects the {@link ExtractLocationParameter} location from the heap {@link JTerm}s.
     *
     * @param selectTerm The parent {@link JTerm}.
     * @param variableTerm The {@link JTerm} with the {@link ProgramVariable}.
     * @param heapLDT The {@link HeapLDT} to use.
     * @param toFill The result {@link Set} to fill.
     * @param objectsToIgnore The objects to ignore.
     * @throws ProofInputException Occurred Exception.
     */
    protected void collectLocationsFromHeapTerms(JTerm selectTerm, JTerm variableTerm,
            HeapLDT heapLDT, Set<ExtractLocationParameter> toFill, Set<JTerm> objectsToIgnore)
            throws ProofInputException {
        if (!objectsToIgnore.contains(selectTerm)
                && !SymbolicExecutionUtil.isSkolemConstant(selectTerm)) {
            ProgramVariable var =
                SymbolicExecutionUtil.getProgramVariable(getServices(), heapLDT, variableTerm);
            if (var != null) {
                if (!isImplicitProgramVariable(var) && !hasFreeVariables(variableTerm)) {
                    if (var.isStatic()) {
                        toFill.add(new ExtractLocationParameter(var, true));
                    } else {
                        if (selectTerm.op() instanceof ProgramVariable) {
                            toFill.add(new ExtractLocationParameter(
                                (ProgramVariable) selectTerm.op(), true));
                        }
                        toFill.add(new ExtractLocationParameter(var, selectTerm));
                    }
                }
            } else {
                JTerm arrayIndex =
                    SymbolicExecutionUtil.getArrayIndex(getServices(), heapLDT, variableTerm);
                if (arrayIndex != null && !hasFreeVariables(arrayIndex)) {
                    if (selectTerm.op() instanceof ProgramVariable) {
                        toFill.add(
                            new ExtractLocationParameter((ProgramVariable) selectTerm.op(), true));
                    }
                    toFill.add(new ExtractLocationParameter(arrayIndex, selectTerm));
                } else {
                    // Nothing to do, since program variable and array index is undefined.
                }
            }
        }
    }

    /**
     * Creates a predicate and a {@link JTerm} which can be used to compute the values defined by
     * the
     * given {@link ExtractLocationParameter}s.
     *
     * @param valueSelectParameter The {@link ExtractLocationParameter}s to compute in the created
     *        {@link JTerm}.
     * @return The created {@link JTerm} which computes the values of the given
     *         {@link ExtractLocationParameter}s.
     */
    protected JTerm createLocationPredicateAndTerm(
            Set<ExtractLocationParameter> valueSelectParameter) {
        List<JTerm> argumentsList = new LinkedList<>();
        int argumentIndex = -1;
        for (ExtractLocationParameter param : valueSelectParameter) {
            argumentsList.add(param.createPreParentTerm());
            param.setParentTermIndexInStatePredicate(++argumentIndex);
            argumentsList.add(param.createPreValueTerm());
            param.setValueTermIndexInStatePredicate(++argumentIndex);
        }
        JTerm[] arguments = argumentsList.toArray(new JTerm[0]);
        Sort[] sorts = new Sort[arguments.length];
        for (int i = 0; i < sorts.length; i++) {
            sorts[i] = arguments[i].sort();
        }
        // Create predicate which will be used in formulas to store the value interested in.
        Function newPredicate =
            new JFunction(new Name(getServices().getTermBuilder().newName("LayoutPredicate")),
                JavaDLTheory.FORMULA, sorts);
        // Create formula which contains the value interested in.
        JTerm newTerm = getServices().getTermBuilder().func(newPredicate, arguments);
        return newTerm;
    }

    /**
     * Returns the {@link Proof} of the analyzed {@link Node}.
     *
     * @return The {@link Proof} of the analyzed {@link Node}.
     */
    protected Proof getProof() {
        return node.proof();
    }

    /**
     * Returns the root {@link Node} of the proof.
     *
     * @return The root {@link Node} of the proof.
     */
    protected Node getRoot() {
        return getProof().root();
    }

    /**
     * Returns the {@link Services} of the analyzed {@link Node}.
     *
     * @return The {@link Services} of the analyzed {@link Node}.
     */
    protected Services getServices() {
        return getProof().getServices();
    }

    /**
     * <p>
     * Instances of this class provides the {@link JTerm} which are required to compute a location
     * (value or association of a given object/state).
     * </p>
     * <p>
     * Instances of this class can be used to compute the values in each memory layout. So they are
     * instantiated during the analyzation phase {@link SymbolicLayoutExtractor#analyse()} once for
     * initial and current memory layout.
     * </p>
     *
     * @author Martin Hentschel
     */
    public class ExtractLocationParameter {
        /**
         * The {@link ProgramVariable} or {@code null} if an array index is used instead.
         */
        private final ProgramVariable programVariable;

        /**
         * The array index or {@code null} if not used.
         */
        private final JTerm arrayIndex;

        /**
         * The array start index or {@code null} if not used.
         */
        private final JTerm arrayStartIndex;

        /**
         * The array end index or {@code null} if not used.
         */
        private final JTerm arrayEndIndex;

        /**
         * An optional parent object represented as {@link JTerm}. If it is {@code null} an
         * {@link IProgramVariable} of the state is represented.
         */
        private final JTerm parentTerm;

        /**
         * The index of the parent argument in the predicate used in side proof to compute the
         * values.
         */
        private int parentTermIndexInStatePredicate;

        /**
         * The index of the value argument in the predicate used in side proof to compute the
         * values.
         */
        private int valueTermIndexInStatePredicate;

        /**
         * The {@link LocationVariable} which is used to make sure that the defined parent object of
         * the initial state is used, because the expression (e.g. {@code x.next}) might refer to
         * different objects in the current state.
         */
        private final LocationVariable preVariable;

        /**
         * Defines if this location should explicitly be shown on the state.
         */
        private final boolean stateMember;

        /**
         * The constant used to query an array range.
         */
        private final JTerm arrayRangeConstant;

        /**
         * The constant representing the fact that no value is available.
         */
        private final JTerm notAValue;

        /**
         * Constructor for cloning purpose.
         *
         * @param original The original {@link ExtractLocationParameter} to clone.
         * @param newParent The new parent {@link JTerm} to be used instead of the original one.
         */
        public ExtractLocationParameter(ExtractLocationParameter original, JTerm newParent) {
            this.programVariable = original.programVariable;
            this.arrayIndex = original.arrayIndex;
            this.parentTerm = OriginTermLabel.removeOriginLabels(newParent, getServices());
            this.parentTermIndexInStatePredicate = original.parentTermIndexInStatePredicate;
            this.valueTermIndexInStatePredicate = original.valueTermIndexInStatePredicate;
            this.preVariable = original.preVariable;
            this.stateMember = original.stateMember;
            this.arrayStartIndex = original.arrayStartIndex;
            this.arrayEndIndex = original.arrayEndIndex;
            this.arrayRangeConstant = original.arrayRangeConstant;
            this.notAValue = original.notAValue;
        }

        /**
         * Constructor.
         *
         * @param programVariable The {@link ProgramVariable}.
         * @param stateMember Defines if this location should explicitly be shown on the state.
         * @throws ProofInputException Occurred Exception.
         */
        public ExtractLocationParameter(ProgramVariable programVariable, boolean stateMember)
                throws ProofInputException {
            this(programVariable, null, stateMember);
        }

        /**
         * Constructor.
         *
         * @param programVariable The {@link ProgramVariable}.
         * @param parentTerm The parent object represented as {@link JTerm}.
         * @throws ProofInputException Occurred Exception.
         */
        public ExtractLocationParameter(ProgramVariable programVariable, JTerm parentTerm)
                throws ProofInputException {
            this(programVariable, parentTerm, false);
        }

        /**
         * Constructor.
         *
         * @param programVariable The {@link ProgramVariable}.
         * @param parentTerm The parent object represented as {@link JTerm}.
         * @param stateMember Defines if this location should explicitly be shown on the state.
         * @throws ProofInputException Occurred Exception.
         */
        protected ExtractLocationParameter(ProgramVariable programVariable, JTerm parentTerm,
                boolean stateMember) throws ProofInputException {
            assert programVariable != null;
            this.programVariable = programVariable;
            this.parentTerm = OriginTermLabel.removeOriginLabels(parentTerm, getServices());
            this.preVariable = createLocationVariable("Pre" + preVariableIndex++,
                parentTerm != null ? parentTerm.sort() : programVariable.sort());
            this.arrayIndex = null;
            this.stateMember = stateMember;
            this.arrayStartIndex = null;
            this.arrayEndIndex = null;
            this.arrayRangeConstant = null;
            this.notAValue = null;
        }

        /**
         * Constructor.
         *
         * @param arrayIndex The array index.
         * @param parentTerm The parent object represented as {@link JTerm}.
         * @throws ProofInputException Occurred Exception.
         */
        public ExtractLocationParameter(JTerm arrayIndex, JTerm parentTerm)
                throws ProofInputException {
            assert parentTerm != null;
            this.programVariable = null;
            this.arrayIndex = OriginTermLabel.removeOriginLabels(arrayIndex, getServices());
            this.parentTerm = OriginTermLabel.removeOriginLabels(parentTerm, getServices());
            this.preVariable =
                createLocationVariable("Pre" + preVariableIndex++, parentTerm.sort());
            this.stateMember = false;
            this.arrayStartIndex = null;
            this.arrayEndIndex = null;
            this.arrayRangeConstant = null;
            this.notAValue = null;
        }

        /**
         * Constructor.
         *
         * @param arrayStartIndex The array start index.
         * @param arrayEndIndex The array end index.
         * @param parentTerm The parent object represented as {@link JTerm}.
         * @throws ProofInputException Occurred Exception.
         */
        public ExtractLocationParameter(JTerm arrayStartIndex, JTerm arrayEndIndex,
                JTerm parentTerm)
                throws ProofInputException {
            assert arrayStartIndex != null;
            assert arrayEndIndex != null;
            assert parentTerm != null;
            this.programVariable = null;
            this.arrayIndex = null;
            this.parentTerm = OriginTermLabel.removeOriginLabels(parentTerm, getServices());
            this.preVariable =
                createLocationVariable("Pre" + preVariableIndex++, parentTerm.sort());
            this.stateMember = false;
            this.arrayStartIndex =
                OriginTermLabel.removeOriginLabels(arrayStartIndex, getServices());
            this.arrayEndIndex = OriginTermLabel.removeOriginLabels(arrayEndIndex, getServices());
            TermBuilder tb = getServices().getTermBuilder();
            Function constantFunction = new JFunction(
                new Name(tb.newName(ExecutionAllArrayIndicesVariable.ARRAY_INDEX_CONSTANT_NAME)),
                getServices().getTypeConverter().getIntegerLDT().targetSort());
            this.arrayRangeConstant = tb.func(constantFunction);
            Function notAValueFunction = new JFunction(
                new Name(tb.newName(ExecutionAllArrayIndicesVariable.NOT_A_VALUE_NAME)),
                JavaDLTheory.ANY);
            this.notAValue = tb.func(notAValueFunction);
        }

        /**
         * Creates a new {@link LocationVariable} with the given name and {@link Sort}.
         *
         * @param name The name of the new variable.
         * @param sort The {@link Sort} of the new variable.
         * @return The created {@link LocationVariable}.
         * @throws ProofInputException Occurred Exception.
         */
        protected LocationVariable createLocationVariable(String name, Sort sort)
                throws ProofInputException {
            return new LocationVariable(new ProgramElementName(name), sort);
        }

        /**
         * Checks if this location should explicitly be shown on the state.
         *
         * @return Show location on state?
         */
        public boolean isStateMember() {
            return stateMember;
        }

        /**
         * Checks if an array index is represented.
         *
         * @return {@code true} is array index, {@code false} is something else.
         */
        public boolean isArrayIndex() {
            return arrayIndex != null;
        }

        /**
         * Checks if an array range is represented.
         *
         * @return {@code true} is array range, {@code false} is something else.
         */
        public boolean isArrayRange() {
            return arrayStartIndex != null && arrayEndIndex != null;
        }

        /**
         * Returns the array index.
         *
         * @return The array index.
         */
        public JTerm getArrayIndex() {
            return arrayIndex;
        }

        /**
         * Returns the array start index.
         *
         * @return The array start index.
         */
        public JTerm getArrayStartIndex() {
            return arrayStartIndex;
        }

        /**
         * Returns the array end index.
         *
         * @return The array end index.
         */
        public JTerm getArrayEndIndex() {
            return arrayEndIndex;
        }

        /**
         * Returns the constant used to query an array range.
         *
         * @return The constant used to query an array range.
         */
        public JTerm getArrayRangeConstant() {
            return arrayRangeConstant;
        }

        /**
         * Returns the constant representing the fact that no value is available.
         *
         * @return The constant representing the fact that no value is available.
         */
        public JTerm getNotAValue() {
            return notAValue;
        }

        /**
         * Returns the pre variable.
         *
         * @return The pre variable.
         */
        public LocationVariable getPreVariable() {
            return preVariable;
        }

        /**
         * Returns the right side of the update created by {@link #createPreUpdate()}.
         *
         * @return The right side of the update created by {@link #createPreUpdate()}.
         */
        public JTerm getPreUpdateTarget() {
            return parentTerm != null ? parentTerm
                    : getServices().getTermBuilder().var(programVariable);
        }

        /**
         * Creates the pre update to make sure that the parent object defined by the expression is
         * evaluated on the initial state because it might be changed in the current state due to
         * updates.
         *
         * @return The created {@link JTerm} with the pre update.
         */
        public JTerm createPreUpdate() {
            JTerm originalTerm = getPreUpdateTarget();
            return getServices().getTermBuilder().elementary(preVariable, originalTerm);
        }

        /**
         * Creates the {@link JTerm} to compute the parent object with help of the pre update.
         *
         * @return The {@link JTerm} to compute the parent object with help of the pre update.
         */
        public JTerm createPreParentTerm() {
            return getServices().getTermBuilder().var(preVariable);
        }

        /**
         * Computes the {@link JTerm} to compute the value with help of the pre update.
         *
         * @return The {@link JTerm} to compute the value with help of the pre update.
         */
        public JTerm createPreValueTerm() {
            final TermBuilder tb = getServices().getTermBuilder();
            if (parentTerm != null) {
                if (isArrayRange()) {
                    JTerm arrayRange = tb.and(tb.geq(arrayRangeConstant, arrayStartIndex),
                        tb.leq(arrayRangeConstant, arrayEndIndex));
                    return tb.ife(arrayRange, tb.dotArr(parentTerm, arrayRangeConstant), notAValue);
                } else if (isArrayIndex()) {
                    return tb.dotArr(parentTerm, arrayIndex);
                } else {
                    if (getServices().getJavaInfo().getArrayLength() == programVariable) {
                        // Special handling for length attribute of arrays
                        Function function =
                            getServices().getTypeConverter().getHeapLDT().getLength();
                        return tb.func(function, createPreParentTerm());
                    } else {
                        Function function =
                            getServices().getTypeConverter().getHeapLDT().getFieldSymbolForPV(
                                (LocationVariable) programVariable, getServices());
                        return tb.dot(programVariable.sort(), createPreParentTerm(), function);
                    }
                }
            } else {
                if (programVariable.isStatic()) {
                    Function function = getServices().getTypeConverter().getHeapLDT()
                            .getFieldSymbolForPV((LocationVariable) programVariable, getServices());
                    return tb.staticDot(programVariable.sort(), function);
                } else {
                    return tb.var(programVariable);
                }
            }
        }

        /**
         * Returns the {@link ProgramVariable} or {@code null} if an array index is used instead.
         *
         * @return The {@link ProgramVariable} or {@code null} if an array index is used instead.
         */
        public ProgramVariable getProgramVariable() {
            return programVariable;
        }

        /**
         * Returns the optional parent object represented as {@link JTerm}. If it is {@code null} an
         * {@link IProgramVariable} of the state is represented.
         *
         * @return The optional parent object represented as {@link JTerm}. If it is {@code null} an
         *         {@link IProgramVariable} of the state is represented.
         */
        public JTerm getParentTerm() {
            return parentTerm;
        }

        /**
         * Returns the index of the parent argument in the predicate used in side proof to compute
         * the values.
         *
         * @return The index of the parent argument in the predicate used in side proof to compute
         *         the values.
         */
        public int getParentTermIndexInStatePredicate() {
            return parentTermIndexInStatePredicate;
        }

        /**
         * Sets the index of the parent argument in the predicate used in side proof to compute the
         * values.
         *
         * @param selectParentTermIndexInStatePredicate The index of the parent argument in the
         *        predicate used in side proof to compute the values.
         */
        public void setParentTermIndexInStatePredicate(int selectParentTermIndexInStatePredicate) {
            this.parentTermIndexInStatePredicate = selectParentTermIndexInStatePredicate;
        }

        /**
         * Returns the index of the value argument in the predicate used in side proof to compute
         * the values.
         *
         * @return The index of the value argument in the predicate used in side proof to compute
         *         the values.
         */
        public int getValueTermIndexInStatePredicate() {
            return valueTermIndexInStatePredicate;
        }

        /**
         * Sets the index of the value argument in the predicate used in side proof to compute the
         * values.
         *
         * @param selectValueTermIndexInStatePredicate The index of the value argument in the
         *        predicate used in side proof to compute the values.
         */
        public void setValueTermIndexInStatePredicate(int selectValueTermIndexInStatePredicate) {
            this.valueTermIndexInStatePredicate = selectValueTermIndexInStatePredicate;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public String toString() {
            if (isArrayRange()) {
                return "[" + arrayStartIndex + " to " + arrayEndIndex + "] "
                    + (parentTerm != null ? " of " + parentTerm : "");
            } else if (isArrayIndex()) {
                return "[" + arrayIndex + "] " + (parentTerm != null ? " of " + parentTerm : "");
            } else {
                return programVariable + (parentTerm != null ? " of " + parentTerm : "");
            }
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public boolean equals(Object obj) {
            if (obj instanceof ExtractLocationParameter other) {
                return Objects.equals(arrayIndex, other.arrayIndex)
                        && stateMember == other.stateMember
                        && Objects.equals(parentTerm, other.parentTerm)
                        && Objects.equals(programVariable, other.programVariable);
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
            result = 31 * result + (arrayIndex != null ? arrayIndex.hashCode() : 0);
            result = 31 * result + (stateMember ? 1 : 0);
            result = 31 * result + (parentTerm != null ? parentTerm.hashCode() : 0);
            result = 31 * result + (programVariable != null ? programVariable.hashCode() : 0);
            return result;
        }
    }

    /**
     * <p>
     * The method starts a side proof with the given arguments to compute the values and objects of
     * the requested memory layout. The {@link ExecutionVariableValuePair} together with the memory
     * layout term defines how to access the side proof result.
     * </p>
     * <p>
     * The next step is the result extraction from side proof which results in a {@link Set} of
     * {@link ExecutionVariableValuePair} instances. Each instance defines a value or association of
     * a parent object or the state itself.
     * </p>
     *
     * @param layoutCondition An optional condition to consider.
     * @param layoutTerm The result term to use in side proof.
     * @param locations The locations to compute in side proof.
     * @param currentLayout {@code true} current layout, {@code false} initial layout.
     * @param simplifyConditions {@code true} simplify conditions, {@code false} do not simplify
     *        conditions.
     * @return The computed {@link ExecutionVariableValuePair}s.
     * @throws ProofInputException Occurred Exception.
     */
    protected Set<ExecutionVariableValuePair> computeVariableValuePairs(JTerm layoutCondition,
            JTerm layoutTerm, Set<ExtractLocationParameter> locations, boolean currentLayout,
            boolean simplifyConditions) throws ProofInputException {
        // Get original updates
        ImmutableList<JTerm> originalUpdates = computeOriginalUpdates(modalityPio, currentLayout);
        // Combine memory layout with original updates
        Map<LocationVariable, JTerm> preUpdateMap = new HashMap<>();
        ImmutableList<JTerm> additionalUpdates = ImmutableSLList.nil();
        for (ExtractLocationParameter evp : locations) {
            additionalUpdates = additionalUpdates.append(evp.createPreUpdate());
            preUpdateMap.put(evp.getPreVariable(), evp.getPreUpdateTarget());
        }
        // Apply array range conditions
        TermBuilder tb = getServices().getTermBuilder();
        // Apply updates
        JTerm updateLayoutTerm = tb.applyParallel(originalUpdates, layoutTerm);
        updateLayoutTerm = tb.applyParallel(additionalUpdates, updateLayoutTerm);
        for (JTerm additionalUpdate : collectAdditionalUpdates()) {
            updateLayoutTerm = tb.apply(additionalUpdate, updateLayoutTerm);
        }
        // New OneStepSimplifier is required because it has an internal state and the default
        // instance can't be used parallel.
        final ProofEnvironment sideProofEnv = SymbolicExecutionSideProofUtil
                .cloneProofEnvironmentWithOwnOneStepSimplifier(getProof(), true);
        Sequent sequent = SymbolicExecutionUtil.createSequentToProveWithNewSuccedent(node,
            modalityPio, layoutCondition, updateLayoutTerm, null, false);
        // Instantiate and run proof
        ApplyStrategyInfo<Proof, Goal> info =
            SymbolicExecutionSideProofUtil.startSideProof(getProof(), sideProofEnv, sequent,
                StrategyProperties.METHOD_CONTRACT, StrategyProperties.LOOP_INVARIANT,
                StrategyProperties.QUERY_ON, StrategyProperties.SPLITTING_NORMAL);
        try {
            if (!info.getProof().closed()) {
                @SuppressWarnings("unchecked")
                Map<JTerm, Set<Goal>>[] paramValueMap = new Map[locations.size()];
                // Group equal values as precondition of computeValueConditions(...)
                for (Goal goal : info.getProof().openGoals()) {
                    JTerm resultTerm =
                        SymbolicExecutionSideProofUtil.extractOperatorTerm(goal, layoutTerm.op());
                    int i = 0;
                    for (ExtractLocationParameter param : locations) {
                        Map<JTerm, Set<Goal>> valueMap = paramValueMap[i];
                        if (valueMap == null) {
                            valueMap = new LinkedHashMap<>();
                            paramValueMap[i] = valueMap;
                        }
                        JTerm value = resultTerm.sub(param.getValueTermIndexInStatePredicate());
                        value = SymbolicExecutionUtil.replaceSkolemConstants(goal.sequent(), value,
                            getServices());
                        // Replace pre variable with original target
                        if (value.op() instanceof LocationVariable) {
                            JTerm originalTarget = preUpdateMap.get(value.op());
                            if (originalTarget != null) {
                                value = originalTarget;
                            }
                        } else if (SymbolicExecutionUtil.isSelect(goal.proof().getServices(),
                            value)) {
                            JTerm object = value.sub(1);
                            if (object.op() instanceof LocationVariable) {
                                JTerm originalTarget = preUpdateMap.get(object.op());
                                if (originalTarget != null) {
                                    value = goal.proof().getServices().getTermBuilder().select(
                                        value.sort(), value.sub(0), originalTarget, value.sub(2));
                                }
                            }
                        }
                        // Update value list
                        Set<Goal> valueList =
                            valueMap.computeIfAbsent(value, k -> new LinkedHashSet<>());
                        valueList.add(goal);
                        i++;
                    }
                }
                // Compute values including conditions
                Map<Node, JTerm> branchConditionCache = new HashMap<>();
                Set<ExecutionVariableValuePair> pairs =
                    new LinkedHashSet<>();
                int i = 0;
                for (ExtractLocationParameter param : locations) {
                    for (Entry<JTerm, Set<Goal>> valueEntry : paramValueMap[i].entrySet()) {
                        Map<Goal, JTerm> conditionsMap = computeValueConditions(
                            valueEntry.getValue(), branchConditionCache, simplifyConditions);
                        if (param.isArrayRange()) {
                            for (Goal goal : valueEntry.getValue()) {
                                if (valueEntry.getKey() != param.getNotAValue()) {
                                    ExecutionVariableValuePair pair =
                                        new ExecutionVariableValuePair(
                                            OriginTermLabel.removeOriginLabels(
                                                param.getArrayStartIndex(), getServices()),
                                            OriginTermLabel.removeOriginLabels(
                                                param.getArrayEndIndex(), getServices()),
                                            OriginTermLabel.removeOriginLabels(
                                                param.getArrayRangeConstant(), getServices()),
                                            OriginTermLabel.removeOriginLabels(
                                                param.getParentTerm(), getServices()),
                                            OriginTermLabel.removeOriginLabels(valueEntry.getKey(),
                                                getServices()),
                                            OriginTermLabel.removeOriginLabels(
                                                conditionsMap.get(goal), getServices()),
                                            param.isStateMember(), goal.node());
                                    pairs.add(pair);
                                }
                            }
                        } else if (param.isArrayIndex()) {
                            for (Goal goal : valueEntry.getValue()) {
                                ExecutionVariableValuePair pair = new ExecutionVariableValuePair(
                                    OriginTermLabel.removeOriginLabels(param.getArrayIndex(),
                                        getServices()),
                                    OriginTermLabel.removeOriginLabels(param.getParentTerm(),
                                        getServices()),
                                    OriginTermLabel.removeOriginLabels(valueEntry.getKey(),
                                        getServices()),
                                    OriginTermLabel.removeOriginLabels(conditionsMap.get(goal),
                                        getServices()),
                                    param.isStateMember(), goal.node());
                                pairs.add(pair);
                            }
                        } else {
                            for (Goal goal : valueEntry.getValue()) {
                                ExecutionVariableValuePair pair =
                                    new ExecutionVariableValuePair(param.getProgramVariable(),
                                        OriginTermLabel.removeOriginLabels(param.getParentTerm(),
                                            getServices()),
                                        OriginTermLabel.removeOriginLabels(valueEntry.getKey(),
                                            getServices()),
                                        OriginTermLabel.removeOriginLabels(conditionsMap.get(goal),
                                            getServices()),
                                        param.isStateMember(), goal.node());
                                pairs.add(pair);
                            }
                        }
                    }
                    i++;
                }
                return pairs;
            } else {
                // Proof is closed, something went wrong, continuation impossible
                return null;
            }
        } finally {
            SymbolicExecutionSideProofUtil.disposeOrStore(
                "Layout computation on node " + node.serialNr() + " with layout term "
                    + ProofSaver.printAnything(layoutTerm, getServices()) + ".",
                info);
        }
    }

    /**
     * Collects additional updates.
     *
     * @return The additional updates.
     */
    protected List<JTerm> collectAdditionalUpdates() {
        return Collections.emptyList();
    }

    /**
     * Computes the original updates.
     *
     * @param pio The {@link PosInOccurrence}.
     * @param currentLayout Is current layout?
     * @return The original updates.
     */
    protected ImmutableList<JTerm> computeOriginalUpdates(
            PosInOccurrence pio,
            boolean currentLayout) {
        ImmutableList<JTerm> originalUpdates;
        if (!currentLayout) {
            originalUpdates = ImmutableSLList.nil();
        } else {
            if (node.proof().root() == node) {
                originalUpdates = SymbolicExecutionUtil.computeRootElementaryUpdates(node);
            } else {
                JTerm originalModifiedFormula = (JTerm) pio.subTerm();
                originalUpdates = TermBuilder.goBelowUpdates2(originalModifiedFormula).first;
            }
        }
        return originalUpdates;
    }

    /**
     * This method computes for all given {@link Goal}s representing the same value their path
     * conditions. A computed path condition consists only of the branch conditions which contribute
     * to the value. Branch conditions of splits which does not contribute to the value are ignored.
     * <p>
     * The implemented algorithm works as follows:
     * <ol>
     * <li>The given {@link Goal}s have to be all {@link Goal}s of the side proof providing the same
     * value. This means that other branches/goals of the side proof result in different branches.
     * </li>
     * <li>A backward iteration on the parent {@link Node}s starting at the {@link Goal}s is
     * performed until the first parent with at least two open children has been found. The
     * iteration is only performed on one goal (or the {@link Node} it stops last) at a time. The
     * iteration is always performed on the {@link Node} with the highest serial number to ensure
     * that different {@link Goal}s will meet at their common parents.</li>
     * <li>When the iteration of all children of a {@link Node} has met, the branch conditions are
     * computed if the split contributes to the value. A split contributes to a value if at least
     * one branch is not reached by backward iteration meaning that its {@link Goal}s provide
     * different values.</li>
     * <li>The backward iteration ends when the root is reached.</li>
     * <li>Finally, for each {@link Goal} is the path condition computed. The path condition is the
     * conjunction over all found branch conditions contributing to the value.</li>
     * </ol>
     *
     * @param valueGoals All {@link Goal}s of the side proof which provide the same value (result).
     * @param branchConditionCache A cache of already computed branch conditions.
     * @param simplifyConditions {@code true} simplify conditions, {@code false} do not simplify
     *        conditions.
     * @return A {@link Map} which contains for each {@link Goal} the computed path condition
     *         consisting of only required splits.
     * @throws ProofInputException Occurred Exception
     */
    protected Map<Goal, JTerm> computeValueConditions(Set<Goal> valueGoals,
            Map<Node, JTerm> branchConditionCache, boolean simplifyConditions)
            throws ProofInputException {
        Comparator<NodeGoal> comparator = (o1, o2) -> {
            return o2.getSerialNr() - o1.getSerialNr(); // Descending order
        };
        // Initialize condition for each goal with true
        Set<Node> untriedRealGoals = new HashSet<>();
        Map<Goal, Set<JTerm>> goalConditions = new HashMap<>();
        List<NodeGoal> sortedBranchLeafs = new LinkedList<>();
        for (Goal goal : valueGoals) {
            CollectionUtil.binaryInsert(sortedBranchLeafs, new NodeGoal(goal), comparator);
            goalConditions.put(goal, new LinkedHashSet<>());
            untriedRealGoals.add(goal.node());
        }
        // Compute branch conditions
        List<NodeGoal> waitingBranchLeafs = new LinkedList<>();
        Map<Node, List<NodeGoal>> splitMap = new HashMap<>();
        while (!sortedBranchLeafs.isEmpty()) {
            // Go back to parent with at least two open goals on maximum outer leaf
            NodeGoal maximumOuterLeaf = sortedBranchLeafs.remove(0); // List is sorted in descending
                                                                     // order
            NodeGoal childGoal = iterateBackOnParents(maximumOuterLeaf,
                !untriedRealGoals.remove(maximumOuterLeaf.getCurrentNode()));
            if (childGoal != null) { // Root is not reached
                waitingBranchLeafs.add(childGoal);
                List<NodeGoal> childGoals =
                    splitMap.computeIfAbsent(childGoal.getParent(), k -> new LinkedList<>());
                childGoals.add(childGoal);
                // Check if parent is reached on all child nodes
                if (isParentReachedOnAllChildGoals(childGoal.getParent(), sortedBranchLeafs)) {
                    // Check if the split contributes to the path condition which is the case if at
                    // least one branch is not present (because it has a different value)
                    if (childGoals.size() != childGoal.getParent().childrenCount()) {
                        // Add branch condition to conditions of all child goals
                        for (NodeGoal nodeGoal : childGoals) {
                            JTerm branchCondition =
                                computeBranchCondition(nodeGoal.getCurrentNode(),
                                    branchConditionCache, simplifyConditions);
                            for (Goal goal : nodeGoal.getStartingGoals()) {
                                Set<JTerm> conditions = goalConditions.get(goal);
                                conditions.add(branchCondition);
                            }
                        }
                    }
                    // Add waiting NodeGoals to working list
                    for (NodeGoal nodeGoal : childGoals) {
                        waitingBranchLeafs.remove(nodeGoal);
                        CollectionUtil.binaryInsert(sortedBranchLeafs, nodeGoal, comparator);
                    }
                }
            }
        }
        // Compute final condition (redundant path conditions are avoided)
        Map<Goal, JTerm> pathConditionsMap = new LinkedHashMap<>();
        for (Entry<Goal, Set<JTerm>> entry : goalConditions.entrySet()) {
            JTerm pathCondition = getServices().getTermBuilder().and(entry.getValue());
            pathConditionsMap.put(entry.getKey(), pathCondition);
        }
        return pathConditionsMap;
    }

    /**
     * Checks if parent backward iteration on all given {@link NodeGoal} has reached the given
     * {@link Node}.
     *
     * @param currentNode The current {@link Node} to check.
     * @param branchLeafs The {@link NodeGoal} on which backward iteration was performed.
     * @return {@code true} All {@link NodeGoal}s have passed the given {@link Node}, {@code false}
     *         if at least one {@link NodeGoal} has not passed the given {@link Node}.
     */
    protected boolean isParentReachedOnAllChildGoals(Node currentNode, List<NodeGoal> branchLeafs) {
        if (!branchLeafs.isEmpty()) {
            return branchLeafs.get(0).getSerialNr() <= currentNode.serialNr();
        } else {
            return true;
        }
    }

    /**
     * Performs a backward iteration on the parents starting at the given {@link NodeGoal} until the
     * first parent with at least two open branches has been found.
     *
     * @param nodeToStartAt The {@link NodeGoal} to start parent backward iteration at.
     * @param force {@code true} first parent is not checked, {@code false} also first parent is
     *        checked.
     * @return The first found parent with at least two open child branches or {@code null} if the
     *         root has been reached.
     */
    protected NodeGoal iterateBackOnParents(NodeGoal nodeToStartAt, boolean force) {
        // Go back to parent with at least two open branches
        Node child = force ? nodeToStartAt.getParent() : nodeToStartAt.getCurrentNode();
        Node parent = child.parent();
        while (parent != null && countOpenChildren(parent) == 1) {
            child = parent;
            parent = child.parent();
        }
        // Store result
        if (parent != null) {
            return new NodeGoal(child, nodeToStartAt.getStartingGoals());
        } else {
            return null;
        }
    }

    /**
     * Counts the number of open child {@link Node}s.
     *
     * @param node The {@link Node} to count its open children.
     * @return The number of open child {@link Node}s.
     */
    protected int countOpenChildren(Node node) {
        int openChildCount = 0;
        for (int i = 0; i < node.childrenCount(); i++) {
            Node child = node.child(i);
            if (!child.isClosed()) {
                openChildCount++;
            }
        }
        return openChildCount;
    }

    /**
     * Utility class used by {@link AbstractUpdateExtractor#computeValueConditions}.
     * Instances of this class store the current {@link Node} and the {@link Goal}s at which
     * backward iteration on parents has started.
     *
     * @author Martin Hentschel
     */
    protected static class NodeGoal {
        /**
         * The current {@link Node}.
         */
        private final Node currentNode;

        /**
         * The {@link Goal}s at which backward iteration has started.
         */
        private final ImmutableList<Goal> startingGoals;

        /**
         * Constructor.
         *
         * @param goal The current {@link Goal} to start backward iteration at.
         */
        public NodeGoal(Goal goal) {
            this(goal.node(), ImmutableSLList.<Goal>nil().prepend(goal));
        }

        /**
         * A reached child node during backward iteration.
         *
         * @param currentNode The current {@link Node}.
         * @param startingGoals The {@link Goal}s at which backward iteration has started.
         */
        public NodeGoal(Node currentNode, ImmutableList<Goal> startingGoals) {
            this.currentNode = currentNode;
            this.startingGoals = startingGoals;
        }

        /**
         * Returns the current {@link Node}.
         *
         * @return The current {@link Node}.
         */
        public Node getCurrentNode() {
            return currentNode;
        }

        /**
         * Returns the parent of {@link #getCurrentNode()}.
         *
         * @return The parent of {@link #getCurrentNode()}.
         */
        public Node getParent() {
            return currentNode.parent();
        }

        /**
         * Returns the serial number of {@link #getCurrentNode()}.
         *
         * @return The serial number of {@link #getCurrentNode()}.
         */
        public int getSerialNr() {
            return currentNode.serialNr();
        }

        /**
         * Returns the {@link Goal}s at which backward iteration has started.
         *
         * @return The {@link Goal}s at which backward iteration has started.
         */
        public ImmutableList<Goal> getStartingGoals() {
            return startingGoals;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public String toString() {
            final StringBuilder sb = new StringBuilder();
            sb.append(currentNode.serialNr());
            sb.append(" starting from goals ");
            sb.append(Strings.formatAsList(startingGoals, "", ", ", "",
                ((java.util.function.Function<Goal, Node>) Goal::node).andThen(Node::serialNr)));
            return sb.toString();
        }
    }

    /**
     * Computes the branch condition if not already present in the cache and stores it in the cache.
     * If the condition is already present in the cache it is returned from it.
     *
     * @param node The {@link Node} to compute its branch condition.
     * @param branchConditionCache The cache of already computed branch conditions.
     * @param simplifyConditions {@code true} simplify conditions, {@code false} do not simplify
     *        conditions.
     * @return The computed branch condition.
     * @throws ProofInputException Occurred Exception.
     */
    protected JTerm computeBranchCondition(Node node, Map<Node, JTerm> branchConditionCache,
            boolean simplifyConditions) throws ProofInputException {
        JTerm result = branchConditionCache.get(node);
        if (result == null) {
            result = SymbolicExecutionUtil.computeBranchCondition(node, simplifyConditions, true);
            branchConditionCache.put(node, result);
        }
        return result;
    }

    /**
     * <p>
     * Represents a location (value or association of a given object/state) in a concrete memory
     * layout of the initial or current state.
     * </p>
     * <p>
     * They are instantiated lazily when a concrete memory layout is requested the first during
     * lazily computation
     * {@link SymbolicLayoutExtractor#lazyComputeLayout}.
     * The instances exists only temporary until the concrete {@link ISymbolicLayout} was created
     * from them.
     * </p>
     *
     * @author Martin Hentschel
     */
    public static class ExecutionVariableValuePair {
        /**
         * The {@link ProgramVariable} or {@code null} if an array index is used instead.
         */
        private final ProgramVariable programVariable;

        /**
         * The array index or {@code null} if not used.
         */
        private final JTerm arrayIndex;

        /**
         * The array start index or {@code null} if not used.
         */
        private final JTerm arrayStartIndex;

        /**
         * The array end index or {@code null} if not used.
         */
        private final JTerm arrayEndIndex;

        /**
         * An optional parent object or {@code null} if it is a value/association of the state.
         */
        private final JTerm parent;

        /**
         * The value or association target.
         */
        private final JTerm value;

        /**
         * Defines if this location should explicitly be shown on the state.
         */
        private final boolean stateMember;

        /**
         * An optional condition under which the value is valid.
         */
        private final JTerm condition;

        /**
         * The {@link Node} on which this result is based on.
         */
        private final Node goalNode;

        /**
         * Constructor.
         *
         * @param programVariable The {@link ProgramVariable}.
         * @param parent An optional parent object or {@code null} if it is a value/association of
         *        the state.
         * @param value The value or association target.
         * @param condition An optional condition under which the value is valid.
         * @param stateMember Defines if this location should explicitly be shown on the state.
         */
        public ExecutionVariableValuePair(ProgramVariable programVariable, JTerm parent,
                JTerm value,
                JTerm condition, boolean stateMember, Node goalNode) {
            assert programVariable != null;
            assert value != null;
            this.programVariable = programVariable;
            this.parent = parent;
            this.value = value;
            this.condition = condition;
            this.arrayIndex = null;
            this.stateMember = stateMember;
            this.goalNode = goalNode;
            this.arrayStartIndex = null;
            this.arrayEndIndex = null;
        }

        /**
         * Constructor.
         *
         * @param arrayIndex The array index.
         * @param parent The parent object.
         * @param value The value or association target.
         * @param condition An optional condition under which the value is valid.
         * @param stateMember Defines if this location should explicitly be shown on the state.
         */
        public ExecutionVariableValuePair(JTerm arrayIndex, JTerm parent, JTerm value,
                JTerm condition,
                boolean stateMember, Node goalNode) {
            assert parent != null;
            assert value != null;
            this.programVariable = null;
            this.arrayIndex = arrayIndex;
            this.parent = parent;
            this.value = value;
            this.condition = condition;
            this.stateMember = stateMember;
            this.goalNode = goalNode;
            this.arrayStartIndex = null;
            this.arrayEndIndex = null;
        }

        /**
         * Constructor.
         *
         * @param arrayStartIndex The array start index.
         * @param arrayEndIndex The array end index.
         * @param arrayRangeConstant The constant used to query an array range.
         * @param parent The parent object.
         * @param value The value or association target.
         * @param condition An optional condition under which the value is valid.
         * @param stateMember Defines if this location should explicitly be shown on the state.
         */
        public ExecutionVariableValuePair(JTerm arrayStartIndex, JTerm arrayEndIndex,
                JTerm arrayRangeConstant, JTerm parent, JTerm value, JTerm condition,
                boolean stateMember, Node goalNode) {
            assert parent != null;
            assert value != null;
            this.programVariable = null;
            this.arrayIndex = arrayRangeConstant;
            this.parent = parent;
            this.value = value;
            this.condition = condition;
            this.stateMember = stateMember;
            this.goalNode = goalNode;
            this.arrayStartIndex = arrayStartIndex;
            this.arrayEndIndex = arrayEndIndex;
        }

        /**
         * Returns the {@link ProgramVariable} or {@code null} if an array index is used instead.
         *
         * @return The {@link ProgramVariable} or {@code null} if an array index is used instead.
         */
        public ProgramVariable getProgramVariable() {
            return programVariable;
        }

        /**
         * Returns the optional parent object or {@code null} if it is a value/association of the
         * state.
         *
         * @return The optional parent object or {@code null} if it is a value/association of the
         *         state.
         */
        public JTerm getParent() {
            return parent;
        }

        /**
         * Returns the value or association target.
         *
         * @return The value or association target.
         */
        public JTerm getValue() {
            return value;
        }

        /**
         * Checks if an array index is represented.
         *
         * @return {@code true} is array index, {@code false} is something else.
         */
        public boolean isArrayIndex() {
            return arrayIndex != null && (arrayStartIndex == null || arrayEndIndex == null);
        }

        /**
         * Checks if an array range is represented.
         *
         * @return {@code true} is array range, {@code false} is something else.
         */
        public boolean isArrayRange() {
            return arrayStartIndex != null && arrayEndIndex != null;
        }

        /**
         * Returns the array index.
         *
         * @return The array index.
         */
        public JTerm getArrayIndex() {
            return arrayIndex;
        }

        /**
         * Returns the array start index.
         *
         * @return The array start index.
         */
        public JTerm getArrayStartIndex() {
            return arrayStartIndex;
        }

        /**
         * Returns the array end index.
         *
         * @return The array end index.
         */
        public JTerm getArrayEndIndex() {
            return arrayEndIndex;
        }

        /**
         * Checks if this location should explicitly be shown on the state.
         *
         * @return Show location on state?
         */
        public boolean isStateMember() {
            return stateMember;
        }

        /**
         * Returns the optional condition under which the value is valid.
         *
         * @return The optional condition under which the value is valid.
         */
        public JTerm getCondition() {
            return condition;
        }

        /**
         * Returns the {@link Node} on which this result is based on.
         *
         * @return The {@link Node} on which this result is based on.
         */
        public Node getGoalNode() {
            return goalNode;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public boolean equals(Object obj) {
            if (obj instanceof ExecutionVariableValuePair other) {
                return isArrayRange()
                        ? (getArrayStartIndex().equals(other.getArrayStartIndex())
                                && getArrayEndIndex().equals(other.getArrayEndIndex()))
                        : (isArrayIndex() ? getArrayIndex().equals(other.getArrayIndex())
                                : getProgramVariable().equals(other.getProgramVariable()))
                                && getParent() != null
                                        ? getParent().equals(other.getParent())
                                        : other.getParent() == null && getCondition() != null
                                                ? getCondition().equals(other.getCondition())
                                                : other.getCondition() == null
                                                        && getValue().equals(other.getValue())
                                                        && getGoalNode()
                                                                .equals(other.getGoalNode());
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
            if (isArrayRange()) {
                result = 31 * result + getArrayStartIndex().hashCode();
                result = 31 * result + getArrayEndIndex().hashCode();
            } else if (isArrayIndex()) {
                result = 31 * result + getArrayIndex().hashCode();
            } else {
                result = 31 * result + getProgramVariable().hashCode();
            }
            result = 31 * result + (getParent() != null ? getParent().hashCode() : 0);
            result = 31 * result + (getCondition() != null ? getCondition().hashCode() : 0);
            result = 31 * result + getValue().hashCode();
            result = 31 * result + getGoalNode().hashCode();
            return result;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public String toString() {
            if (isArrayRange()) {
                return "[" + getArrayIndex() + "]" + " between " + getArrayStartIndex() + " and "
                    + getArrayEndIndex() + (getParent() != null ? " of " + getParent() : "")
                    + " is " + getValue()
                    + (getCondition() != null ? " under condition " + getCondition() : "")
                    + " at goal " + goalNode.serialNr();
            } else if (isArrayIndex()) {
                return "[" + getArrayIndex() + "]"
                    + (getParent() != null ? " of " + getParent() : "") + " is " + getValue()
                    + (getCondition() != null ? " under condition " + getCondition() : "")
                    + " at goal " + goalNode.serialNr();
            } else {
                return getProgramVariable() + (getParent() != null ? " of " + getParent() : "")
                    + " is " + getValue()
                    + (getCondition() != null ? " under condition " + getCondition() : "")
                    + " at goal " + goalNode.serialNr();
            }
        }
    }
}
