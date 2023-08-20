/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.merge;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashSet;
import javax.annotation.Nonnull;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.merge.MergeProcedure.ValuesMergeResult;
import de.uka.ilkd.key.rule.merge.procedures.MergeByIfThenElse;
import de.uka.ilkd.key.rule.merge.procedures.MergeIfThenElseAntecedent;
import de.uka.ilkd.key.rule.merge.procedures.MergeTotalWeakening;
import de.uka.ilkd.key.rule.merge.procedures.MergeWithLatticeAbstraction;
import de.uka.ilkd.key.rule.merge.procedures.MergeWithPredicateAbstraction;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;
import de.uka.ilkd.key.util.mergerule.SymbolicExecutionState;
import de.uka.ilkd.key.util.mergerule.SymbolicExecutionStateWithProgCnt;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import static de.uka.ilkd.key.util.mergerule.MergeRuleUtils.clearSemisequent;
import static de.uka.ilkd.key.util.mergerule.MergeRuleUtils.closeMergePartnerGoal;
import static de.uka.ilkd.key.util.mergerule.MergeRuleUtils.getConjunctiveElementsFor;
import static de.uka.ilkd.key.util.mergerule.MergeRuleUtils.getLocationVariables;
import static de.uka.ilkd.key.util.mergerule.MergeRuleUtils.getUpdateLeftSideLocations;
import static de.uka.ilkd.key.util.mergerule.MergeRuleUtils.getUpdateRightSideFor;
import static de.uka.ilkd.key.util.mergerule.MergeRuleUtils.isProvableWithSplitting;
import static de.uka.ilkd.key.util.mergerule.MergeRuleUtils.isUpdateNormalForm;
import static de.uka.ilkd.key.util.mergerule.MergeRuleUtils.sequentToSETriple;

/**
 * Base for implementing merge rules. Extend this class, implement method mergeValuesInStates(...)
 * and register in class JavaProfile.
 * <p>
 *
 * The rule is applicable if the chosen subterm has the form { x := v || ... } PHI and there are
 * potential merge candidates.
 * <p>
 *
 * Any rule application returned will be incomplete; completion is handled by
 * de.uka.ilkd.key.gui.mergerule.MergeRuleCompletion.
 *
 * @author Dominic Scheurer
 *
 * @see MergeRuleUtils
 * @see MergeTotalWeakening
 * @see MergeByIfThenElse
 * @see MergeIfThenElseAntecedent
 * @see MergeWithLatticeAbstraction
 * @see MergeWithPredicateAbstraction
 * @see de.uka.ilkd.key.gui.mergerule.MergeRuleCompletion
 * @see de.uka.ilkd.key.gui.mergerule.MergePartnerSelectionDialog
 */
public class MergeRule implements BuiltInRule {
    public static final MergeRule INSTANCE = new MergeRule();

    private static final String DISPLAY_NAME = "MergeRule";
    private static final Name RULE_NAME = new Name(DISPLAY_NAME);

    /**
     * If set to true, merge rules are expected to check the equivalence for right sides (for
     * preserving idempotency) only on a pure syntactical basis. If set to false, they are allowed
     * to do a proof to check the equivalence in the respective contexts.
     */
    protected static final boolean RIGHT_SIDE_EQUIVALENCE_ONLY_SYNTACTICAL = true;

    /**
     * Thresholds the maximum depth of right sides in updates for which an equivalence proof is
     * started.
     *
     * We skip the check for equal valuation of this variable if the depth threshold is exceeded by
     * one of the right sides. Experiments show a very big time overhead from a depth of about 8-10
     * on, or sometimes even earlier.
     */
    private static final int MAX_UPDATE_TERM_DEPTH_FOR_CHECKING = 8;

    /**
     * Time threshold in milliseconds for the automatic simplification of formulae (side proofs are
     * stopped after that amount of time).
     */
    private static final int SIMPLIFICATION_TIMEOUT_MS = 2000;

    /**
     * {@link MergeRule} is a Singleton class, therefore constructor only package-wide visible.
     */
    MergeRule() {
    }

    @Override
    public Name name() {
        return RULE_NAME;
    }

    @Override
    public String displayName() {
        return DISPLAY_NAME;
    }

    @Override
    public String toString() {
        return displayName();
    }

    @Nonnull
    @Override
    public final ImmutableList<Goal> apply(Goal goal, final Services services, RuleApp ruleApp)
            throws RuleAbortException {

        final MergeRuleBuiltInRuleApp mergeRuleApp = (MergeRuleBuiltInRuleApp) ruleApp;

        if (!mergeRuleApp.complete()) {
            throw new RuleAbortException("Merge rule not complete");
        }

        // The number of goals needed for side conditions related to
        // manually chosen lattice elements.
        final int numSideConditionsToProve =
            mergeRuleApp.getConcreteRule() instanceof MergeWithLatticeAbstraction
                    ? ((MergeWithLatticeAbstraction) mergeRuleApp.getConcreteRule())
                            .getUserChoices().size() * (mergeRuleApp.getMergePartners().size() + 1)
                    : 0;

        // New goals are reversed to make sure that they are displayed in the
        // order expected by the user.
        final ImmutableList<Goal> newGoals = goal.split(1 + numSideConditionsToProve).reverse();
        final Goal newGoal = newGoals.head();

        final TermBuilder tb = services.getTermBuilder();
        final MergeProcedure mergeRule = mergeRuleApp.getConcreteRule();
        final Node currentNode = newGoal.node();
        final ImmutableList<MergePartner> mergePartners = mergeRuleApp.getMergePartners();

        final SymbolicExecutionStateWithProgCnt thisSEState = mergeRuleApp.getMergeSEState();

        final ImmutableList<SymbolicExecutionState> mergePartnerStates =
            mergeRuleApp.getMergePartnerStates();

        // The merge loop
        SymbolicExecutionState mergedState =
            new SymbolicExecutionState(thisSEState.first, thisSEState.second, newGoal.node());
        LinkedHashSet<Name> newNames = new LinkedHashSet<>();
        LinkedHashSet<Term> sideConditionsToProve = new LinkedHashSet<>();
        HashMap<Node, SymbolicExecutionState> mergePartnerNodesToStates = new HashMap<>();

        int cnt = 0;
        for (SymbolicExecutionState state : mergePartnerStates) {
            mergeRuleApp.fireProgressChange(cnt++);

            final Pair<SymbolicExecutionState, SymbolicExecutionState> noClash = //
                MergeRuleUtils.handleNameClashes(mergedState, state, services);

            mergedState = noClash.first;
            state = noClash.second;

            mergePartnerNodesToStates.put(state.getCorrespondingNode(), state);

            Triple<SymbolicExecutionState, LinkedHashSet<Name>, LinkedHashSet<Term>> mergeResult =
                mergeStates(mergeRule, mergedState, state, thisSEState.third,
                    mergeRuleApp.getDistinguishingFormula(), services);
            newNames.addAll(mergeResult.second);
            sideConditionsToProve.addAll(mergeResult.third);

            mergedState = mergeResult.first;
            mergedState.setCorrespondingNode(newGoal.node());
        }

        final Term resultPathCondition = mergedState.second;

        // NOTE (DS): The following simplification has been commented
        // out since it was usually not successful and consumed an
        // inadequate amount of time.

        // final Term previousResultPathCondition = resultPathCondition;
        // resultPathCondition =
        // trySimplify(services.getProof(), resultPathCondition, true);

        // Close partner goals
        for (MergePartner mergePartner : mergePartners) {
            closeMergePartnerGoal(newGoal.node(), mergePartner.getGoal(), mergePartner.getPio(),
                mergedState, mergePartnerNodesToStates.get(mergePartner.getGoal().node()),
                thisSEState.third, newNames);
        }

        // Delete previous sequents
        clearSemisequent(newGoal, true);
        clearSemisequent(newGoal, false);

        // We need to remove all partially instantiated no pos taclets from
        // the new goal that at least one of the merge the partners does not
        // also have. Otherwise, this would be a soundness problem (e.g. in
        // the case of insert_hidden taclets). However, taclets that are present
        // in all partner goals may be safely kept.
        final ArrayList<NoPosTacletApp> partInstNoPosTacletsToRemove =
            new ArrayList<>();
        newGoal.indexOfTaclets().getPartialInstantiatedApps().forEach(app -> {
            for (final MergePartner mergePartner : mergePartners) {
                if (!mergePartner.getGoal().indexOfTaclets().getPartialInstantiatedApps()
                        .contains(app)) {
                    partInstNoPosTacletsToRemove.add(app);
                    break;
                }
            }
        });

        newGoal.indexOfTaclets().removeTaclets(partInstNoPosTacletsToRemove);

        // Add new antecedent (path condition)
        for (Term antecedentFormula : getConjunctiveElementsFor(resultPathCondition)) {
            final SequentFormula newAntecedent = new SequentFormula(antecedentFormula);
            newGoal.addFormula(newAntecedent, true, false);
        }

        // Add new succedent (symbolic state & program counter)
        final Term succedentFormula = tb.apply(mergedState.first, thisSEState.third);
        final SequentFormula newSuccedent = new SequentFormula(succedentFormula);
        newGoal.addFormula(newSuccedent,
            new PosInOccurrence(newSuccedent, PosInTerm.getTopLevel(), false));

        // The following line has the only effect of emptying the
        // name recorder -- the name recorder for currentNode will
        // be filled after partner node closing. The purpose of this
        // measure is to avoid new names of merge nodes being added as
        // new names of the partners.
        services.saveNameRecorder(currentNode);

        // Register new names
        for (Name newName : newNames) {
            services.addNameProposal(newName);
        }

        // Add new goals for side conditions that have to be proven
        if (sideConditionsToProve.size() > 0) {
            final Iterator<Term> sideCondIt = sideConditionsToProve.iterator();

            int i = 0;
            for (Goal sideConditionGoal : newGoals) {
                if (i == 0) {
                    i++;

                    sideConditionGoal.node().getNodeInfo().setBranchLabel("Merge Result");
                    continue;
                }

                sideConditionGoal.node().getNodeInfo().setBranchLabel("Merge is valid (" + i + ")");

                clearSemisequent(sideConditionGoal, true);
                clearSemisequent(sideConditionGoal, false);
                final Term sideCondition = sideCondIt.next();

                sideConditionGoal.addFormula(new SequentFormula(sideCondition),
                    new PosInOccurrence(newSuccedent, PosInTerm.getTopLevel(), false));

                i++;
            }
        }

        return newGoals;
    }

    /**
     * Merges two SE states (U1,C1,p) and (U2,C2,p) according to the method
     * {@link MergeRule#mergeValuesInStates(LocationVariable, SymbolicExecutionState, Term, SymbolicExecutionState, Term, Services)}
     * . p must be the same in both states, so it is supplied separately.
     * <p>
     *
     * Override this method for special merge procedures.
     *
     * @param mergeRule The merge procedure to use for the merge.
     * @param state1 First state to merge.
     * @param state2 Second state to merge.
     * @param programCounter The formula \&lt;{ ... }\&gt; phi consisting of the common program
     *        counter and the post condition.
     * @param distinguishingFormula The user-specified distinguishing formula. May be null (for
     *        automatic generation).
     * @param services The services object.
     * @return A new merged SE state (U*,C*) which is a weakening of the original states.
     */
    @SuppressWarnings("unused")
    /* For deactivated equiv check */
    protected Triple<SymbolicExecutionState, LinkedHashSet<Name>, LinkedHashSet<Term>> mergeStates(
            MergeProcedure mergeRule, SymbolicExecutionState state1, SymbolicExecutionState state2,
            Term programCounter, Term distinguishingFormula, Services services) {

        final TermBuilder tb = services.getTermBuilder();

        // Newly introduced names
        final LinkedHashSet<Name> newNames = new LinkedHashSet<>();

        // Side conditions remaining to be proven, e.g. after predicate
        // abstraction.
        final LinkedHashSet<Term> sideConditionsToProve = new LinkedHashSet<>();

        // Construct path condition as (optimized) disjunction
        // NOTE: Deactivated this; This optimization can create shorter
        // formulas, but is very time consumptive. At the end, the result does
        // not always perform better than within the unoptimized version.
        final Term newPathCondition = MergeRuleUtils.createSimplifiedDisjunctivePathCondition(
            state1.second, state2.second, services, SIMPLIFICATION_TIMEOUT_MS);

        ImmutableSet<LocationVariable> progVars = DefaultImmutableSet.nil();

        // Collect program variables in Java block
        progVars = progVars.union(getLocationVariables(programCounter, services));
        // Collect program variables in update
        progVars = progVars.union(getUpdateLeftSideLocations(state1.first));
        progVars = progVars.union(getUpdateLeftSideLocations(state2.first));

        ImmutableList<Term> newElementaryUpdates = ImmutableSLList.nil();

        // New constraints on introduced Skolem constants
        Term newAdditionalConstraints = null;

        for (LocationVariable v : progVars) {

            Term rightSide1 = getUpdateRightSideFor(state1.first, v);
            Term rightSide2 = getUpdateRightSideFor(state2.first, v);

            if (rightSide1 == null) {
                rightSide1 = tb.var(v);
            }

            if (rightSide2 == null) {
                rightSide2 = tb.var(v);
            }

            // Check if location v is set to different value in both states.

            // Easy check: Term equality
            boolean proofClosed = rightSide1.equalsModRenaming(rightSide2);

            // We skip the check for equal valuation of this variable if
            // the depth threshold is exceeded by one of the right sides.
            // Experiments show a very big time overhead from a depth of
            // about 8-10 on, or sometimes even earlier.
            if (rightSide1.depth() <= MAX_UPDATE_TERM_DEPTH_FOR_CHECKING
                    && rightSide2.depth() <= MAX_UPDATE_TERM_DEPTH_FOR_CHECKING && !proofClosed
                    && !MergeRule.RIGHT_SIDE_EQUIVALENCE_ONLY_SYNTACTICAL) {

                Term predicateTerm =
                    tb.func(new Function(new Name("P"), Sort.FORMULA, v.sort()), tb.var(v));
                Term appl1 = tb.apply(state1.first, predicateTerm);
                Term appl2 = tb.apply(state2.first, predicateTerm);
                Term toProve = tb.and(tb.imp(appl1, appl2), tb.imp(appl2, appl1));

                proofClosed = isProvableWithSplitting(toProve, services, SIMPLIFICATION_TIMEOUT_MS);
            }

            if (proofClosed) {

                // Arbitrary choice: Take value of first state if
                // this does not equal the program variable itself
                if (!rightSide1.equals(tb.var(v))) {
                    newElementaryUpdates =
                        newElementaryUpdates.prepend(tb.elementary(v, rightSide1));
                }

            } else {

                // Apply merge procedure: Different values

                Sort heapSort = services.getNamespaces().sorts().lookup("Heap");

                if (v.sort().equals(heapSort)) {

                    ValuesMergeResult mergedHeaps = mergeHeaps(mergeRule, v, rightSide1, rightSide2,
                        state1, state2, distinguishingFormula, services);

                    newElementaryUpdates =
                        newElementaryUpdates.prepend(tb.elementary(v, mergedHeaps.getMergeVal()));
                    if (newAdditionalConstraints == null) {
                        newAdditionalConstraints = tb.and(mergedHeaps.getNewConstraints());
                    } else {
                        newAdditionalConstraints = tb.and(newAdditionalConstraints,
                            tb.and(mergedHeaps.getNewConstraints()));
                    }

                    newNames.addAll(mergedHeaps.getNewNames());
                    sideConditionsToProve.addAll(mergedHeaps.getSideConditions());

                } else {

                    ValuesMergeResult mergedVal = mergeRule.mergeValuesInStates(tb.var(v), state1,
                        rightSide1, state2, rightSide2, distinguishingFormula, services);

                    newNames.addAll(mergedVal.getNewNames());
                    sideConditionsToProve.addAll(mergedVal.getSideConditions());

                    newElementaryUpdates =
                        newElementaryUpdates.prepend(tb.elementary(v, mergedVal.getMergeVal()));

                    if (newAdditionalConstraints == null) {
                        newAdditionalConstraints = tb.and(mergedVal.getNewConstraints());
                    } else {
                        newAdditionalConstraints =
                            tb.and(newAdditionalConstraints, tb.and(mergedVal.getNewConstraints()));
                    }

                } // end else of if (v.sort().equals(heapSort))

            } // end else of if (proofClosed)

        } // end for (LocationVariable v : progVars)

        // Construct weakened symbolic state
        Term newSymbolicState = tb.parallel(newElementaryUpdates);

        // Note: We apply the symbolic state to the new constraints to enable
        // merge techniques, in particular predicate abstraction, to make
        // references to the values of other variables involved in the merge.
        return new Triple<>(
            new SymbolicExecutionState(newSymbolicState,
                newAdditionalConstraints == null ? newPathCondition
                        : tb.and(newPathCondition,
                            tb.apply(newSymbolicState, newAdditionalConstraints))),
            newNames, sideConditionsToProve);

    }

    /**
     * Merges two heaps in a zip-like procedure. The fallback is an if-then-else construct that is
     * tried to be shifted as far inwards as possible.
     * <p>
     *
     * Override this method for specialized heap merge procedures.
     *
     * @param heapVar The heap variable for which the values should be merged.
     * @param heap1 The first heap term.
     * @param heap2 The second heap term.
     * @param state1 SE state for the first heap term.
     * @param state2 SE state for the second heap term
     * @param services The services object.
     * @param distinguishingFormula The user-specified distinguishing formula. May be null (for
     *        automatic generation).
     * @return A merged heap term.
     */
    protected ValuesMergeResult mergeHeaps(final MergeProcedure mergeRule,
            final LocationVariable heapVar, final Term heap1, final Term heap2,
            final SymbolicExecutionState state1, final SymbolicExecutionState state2,
            Term distinguishingFormula, final Services services) {

        final TermBuilder tb = services.getTermBuilder();
        ImmutableSet<Term> newConstraints = DefaultImmutableSet.nil();
        LinkedHashSet<Name> newNames = new LinkedHashSet<>();

        final LinkedHashSet<Term> sideConditionsToProve = new LinkedHashSet<>();

        if (heap1.equals(heap2)) {
            // Keep equal heaps
            return new ValuesMergeResult(newConstraints, heap1, newNames, sideConditionsToProve);
        }

        if (!(heap1.op() instanceof Function) || !(heap2.op() instanceof Function)) {
            // Covers the case of two different symbolic heaps
            return new ValuesMergeResult(newConstraints,
                MergeByIfThenElse.createIfThenElseTerm(state1, state2, heap1, heap2,
                    distinguishingFormula, services),
                newNames, sideConditionsToProve);
        }

        final Function storeFunc = services.getNamespaces().functions().lookup("store");
        final Function createFunc =
            services.getNamespaces().functions().lookup("create");
        // Note: Check if there are other functions that should be covered.
        // Unknown functions are treated by if-then-else procedure.

        if (heap1.op().equals(storeFunc)
                && heap2.op().equals(storeFunc)) {

            // Store operations.

            // Decompose the heap operations.
            final Term subHeap1 = heap1.sub(0);
            final Term pointer1 = heap1.sub(1);
            final Term field1 = heap1.sub(2);
            final Term value1 = heap1.sub(3);

            final Term subHeap2 = heap2.sub(0);
            final Term pointer2 = heap2.sub(1);
            final Term field2 = heap2.sub(2);
            final Term value2 = heap2.sub(3);

            if (pointer1.equals(pointer2) && field1.equals(field2)) {
                // Potential for deep merge: Access of same object / field.

                ValuesMergeResult mergedSubHeap = mergeHeaps(mergeRule, heapVar, subHeap1, subHeap2,
                    state1, state2, distinguishingFormula, services);
                newConstraints = newConstraints.union(mergedSubHeap.getNewConstraints());
                newNames.addAll(mergedSubHeap.getNewNames());
                sideConditionsToProve.addAll(mergedSubHeap.getSideConditions());

                Term mergedVal = null;

                if (value1.equals(value2)) {
                    // Idempotency...
                    mergedVal = value1;

                } else {

                    ValuesMergeResult mergedValAndConstr = mergeRule.mergeValuesInStates(field1,
                        state1, value1, state2, value2, distinguishingFormula, services);

                    newConstraints = newConstraints.union(mergedValAndConstr.getNewConstraints());
                    newNames.addAll(mergedValAndConstr.getNewNames());
                    sideConditionsToProve.addAll(mergedValAndConstr.getSideConditions());
                    mergedVal = mergedValAndConstr.getMergeVal();

                }

                return new ValuesMergeResult(newConstraints, tb.func((Function) heap1.op(),
                    mergedSubHeap.getMergeVal(), heap1.sub(1), field1, mergedVal), newNames,
                    sideConditionsToProve);

            } // end if (pointer1.equals(pointer2) && field1.equals(field2))

        } else if (heap1.op().equals(createFunc)
                && heap2.op().equals(createFunc)) {

            // Create operations.

            // Decompose the heap operations.
            Term subHeap1 = heap1.sub(0);
            Term pointer1 = heap1.sub(1);

            Term subHeap2 = heap2.sub(0);
            Term pointer2 = heap2.sub(1);

            if (pointer1.equals(pointer2)) {
                // Same objects are created: merge.

                ValuesMergeResult mergedSubHeap = mergeHeaps(mergeRule, heapVar, subHeap1, subHeap2,
                    state1, state2, distinguishingFormula, services);
                newConstraints = newConstraints.union(mergedSubHeap.getNewConstraints());
                newNames.addAll(mergedSubHeap.getNewNames());
                sideConditionsToProve.addAll(mergedSubHeap.getSideConditions());

                return new ValuesMergeResult(newConstraints,
                    tb.func((Function) heap1.op(), mergedSubHeap.getMergeVal(), pointer1), newNames,
                    sideConditionsToProve);
            }

            // "else" case is fallback at end of method:
            // if-then-else of heaps.

        } // end else of else if (((Function) heap1.op()).equals(createFunc) &&
          // ((Function) heap2.op()).equals(createFunc))

        return new ValuesMergeResult(newConstraints, MergeByIfThenElse.createIfThenElseTerm(state1,
            state2, heap1, heap2, distinguishingFormula, services), newNames,
            sideConditionsToProve);

    }

    /**
     * We admit top level formulas of the form \&lt;{ ... }\&gt; phi and U \&lt;{ ... }\&gt; phi,
     * where U must be an update in normal form, i.e. a parallel update of elementary updates.
     *
     * @param goal Current goal.
     * @param pio Position of selected sequent formula.
     * @return true iff a suitable top level formula for merging.
     */
    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        return isOfAdmissibleForm(goal, pio, true);
    }

    /**
     * We admit top level formulas of the form \&lt;{ ... }\&gt; phi and U \&lt;{ ... }\&gt; phi,
     * where U must be an update in normal form, i.e. a parallel update of elementary updates. We
     * require that phi does not contain a Java block.
     *
     * @param goal Current goal.
     * @param pio Position of selected sequent formula.
     * @param doMergePartnerCheck Checks for available merge partners iff this flag is set to true.
     * @return true iff a suitable top level formula for merging.
     */
    public static boolean isOfAdmissibleForm(Goal goal, PosInOccurrence pio,
            boolean doMergePartnerCheck) {
        // We admit top level formulas of the form \<{ ... }\> phi
        // and U \<{ ... }\> phi, where U must be an update
        // in normal form, i.e. a parallel update of elementary
        // updates.

        if (pio == null || !pio.isTopLevel()) {
            return false;
        }

        Term selected = pio.subTerm();

        Term termAfterUpdate = selected;

        if (selected.op() instanceof UpdateApplication) {
            Term update = selected.sub(0);

            if (isUpdateNormalForm(update) && selected.subs().size() > 1) {
                termAfterUpdate = selected.sub(1);
            } else {
                return false;
            }
        } else {
            // NOTE: This disallows merges for formulae without updates
            // in front. In principle, merges are possible for
            // arbitrary formulae, but this significantly slows
            // down the JavaCardDLStrategy since for every formula,
            // all goals in the tree are searched. For the intended
            // applications, it suffices to allow merges just for
            // formulae of the form {U}\phi.
            return false;
        }

        // Term after update must have the form "phi" or "\<{...}\> phi" or
        // "\[{...}\]", where phi must not contain a Java block.
        if (termAfterUpdate.op() instanceof Modality
                && !termAfterUpdate.sub(0).javaBlock().equals(JavaBlock.EMPTY_JAVABLOCK)) {
            return false;
        } else if (termAfterUpdate.op() instanceof UpdateApplication) {
            return false;
        }

        return !doMergePartnerCheck || findPotentialMergePartners(goal, pio).size() > 0;

    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pio, TermServices services) {
        return new MergeRuleBuiltInRuleApp(this, pio);
    }

    /**
     * Finds all suitable merge partners
     *
     * @param goal Current goal to merge.
     * @param pio Position of update-program counter formula in goal.
     * @param start Node to start the search with.
     * @param services The services object.
     * @return A list of suitable merge partners. May be empty if none exist.
     */
    public static ImmutableList<MergePartner> findPotentialMergePartners(Goal goal,
            PosInOccurrence pio) {

        final Services services = goal.proof().getServices();

        final ImmutableList<Goal> allGoals = services.getProof().openGoals();

        final Triple<Term, Term, Term> ownSEState = sequentToSETriple(goal.node(), pio, services);

        // Find potential partners -- for which isApplicable is true and
        // they have the same program counter (and post condition).
        ImmutableList<MergePartner> potentialPartners = ImmutableSLList.nil();

        for (final Goal g : allGoals) {
            if (!g.equals(goal) && !g.isLinked()) {
                Semisequent succedent = g.sequent().succedent();
                for (int i = 0; i < succedent.size(); i++) {
                    final SequentFormula f = succedent.get(i);

                    final PosInTerm pit = PosInTerm.getTopLevel();

                    final PosInOccurrence gPio = new PosInOccurrence(f, pit, false);
                    if (isOfAdmissibleForm(g, gPio, false)) {
                        final Triple<Term, Term, Term> partnerSEState =
                            sequentToSETriple(g.node(), gPio, services);

                        if (ownSEState.third.equals(partnerSEState.third)) {

                            potentialPartners =
                                potentialPartners.prepend(new MergePartner(g, gPio));

                        }
                    }
                }
            }
        }

        return potentialPartners;
    }

    @FunctionalInterface
    public interface MergeRuleProgressListener {
        void signalProgress(int progress);
    }

}
