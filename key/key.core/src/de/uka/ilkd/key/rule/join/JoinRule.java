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

package de.uka.ilkd.key.rule.join;

import static de.uka.ilkd.key.util.joinrule.JoinRuleUtils.clearSemisequent;
import static de.uka.ilkd.key.util.joinrule.JoinRuleUtils.closeJoinPartnerGoal;
import static de.uka.ilkd.key.util.joinrule.JoinRuleUtils.createSimplifiedDisjunctivePathCondition;
import static de.uka.ilkd.key.util.joinrule.JoinRuleUtils.getConjunctiveElementsFor;
import static de.uka.ilkd.key.util.joinrule.JoinRuleUtils.getLocationVariables;
import static de.uka.ilkd.key.util.joinrule.JoinRuleUtils.getUpdateLeftSideLocations;
import static de.uka.ilkd.key.util.joinrule.JoinRuleUtils.getUpdateRightSideFor;
import static de.uka.ilkd.key.util.joinrule.JoinRuleUtils.isProvableWithSplitting;
import static de.uka.ilkd.key.util.joinrule.JoinRuleUtils.isUpdateNormalForm;
import static de.uka.ilkd.key.util.joinrule.JoinRuleUtils.sequentToSEPair;
import static de.uka.ilkd.key.util.joinrule.JoinRuleUtils.sequentToSETriple;

import java.util.HashMap;
import java.util.LinkedList;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.JavaProgramElement;
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
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.ProgVarReplacer;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.join.procedures.JoinIfThenElse;
import de.uka.ilkd.key.rule.join.procedures.JoinIfThenElseAntecedent;
import de.uka.ilkd.key.rule.join.procedures.JoinWeaken;
import de.uka.ilkd.key.rule.join.procedures.JoinWithLatticeAbstraction;
import de.uka.ilkd.key.rule.join.procedures.JoinWithSignLattice;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;
import de.uka.ilkd.key.util.joinrule.JoinRuleUtils;
import de.uka.ilkd.key.util.joinrule.ProgramVariablesMatchVisitor;
import de.uka.ilkd.key.util.joinrule.SymbolicExecutionState;
import de.uka.ilkd.key.util.joinrule.SymbolicExecutionStateWithProgCnt;

/**
 * Base for implementing join rules. Extend this class, implement method
 * joinValuesInStates(...) and register in class JavaProfile.
 * <p>
 * 
 * The rule is applicable if the chosen subterm has the form { x := v || ... }
 * PHI and there are potential join candidates.
 * <p>
 * 
 * Any rule application returned will be incomplete; completion is handled by
 * de.uka.ilkd.key.gui.joinrule.JoinRuleCompletion.
 * 
 * @author Dominic Scheurer
 * 
 * @see JoinRuleUtils
 * @see JoinWeaken
 * @see JoinIfThenElse
 * @see JoinIfThenElseAntecedent
 * @see JoinWithLatticeAbstraction
 * @see JoinWithSignLattice
 * @see de.uka.ilkd.key.gui.joinrule.JoinRuleCompletion
 * @see de.uka.ilkd.key.gui.joinrule.JoinPartnerSelectionDialog
 */
public class JoinRule implements BuiltInRule {
    public static final JoinRule INSTANCE = new JoinRule();

    private static final String DISPLAY_NAME = "JoinRule";
    private static final Name RULE_NAME = new Name(DISPLAY_NAME);

    /**
     * If set to true, join rules are expected to check the equivalence for
     * right sides (for preserving idempotency) only on a pure syntactical
     * basis. If set to false, they are allowed to do a proof to check the
     * equivalence in the respective contexts.
     */
    protected static final boolean RIGHT_SIDE_EQUIVALENCE_ONLY_SYNTACTICAL =
            true;

    /**
     * Thresholds the maximum depth of right sides in updates for which an
     * equivalence proof is started.
     * 
     * We skip the check for equal valuation of this variable if the depth
     * threshold is exceeded by one of the right sides. Experiments show a very
     * big time overhead from a depth of about 8-10 on, or sometimes even
     * earlier.
     */
    private static final int MAX_UPDATE_TERM_DEPTH_FOR_CHECKING = 8;

    /**
     * Time threshold in milliseconds for the automatic simplification of
     * formulae (side proofs are stopped after that amount of time).
     */
    private static final int SIMPLIFICATION_TIMEOUT_MS = 2000;

    /**
     * JoinRule is a Singleton class, therefore constructor only package-wide
     * visible.
     */
    JoinRule() {
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

    @Override
    public final ImmutableList<Goal> apply(Goal goal, final Services services,
            RuleApp ruleApp) throws RuleAbortException {

        final JoinRuleBuiltInRuleApp joinRuleApp =
                (JoinRuleBuiltInRuleApp) ruleApp;

        if (!joinRuleApp.complete()) {
            return null;
        }

        final ImmutableList<Goal> newGoals = goal.split(1);
        final Goal newGoal = newGoals.head();

        final TermBuilder tb = services.getTermBuilder();
        final JoinProcedure joinRule = joinRuleApp.getConcreteRule();
        final Node currentNode = newGoal.node();
        final ImmutableList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> joinPartners =
                joinRuleApp.getJoinPartners();

        final SymbolicExecutionStateWithProgCnt thisSEState =
                joinRuleApp.getJoinSEState();

        ImmutableList<SymbolicExecutionState> joinPartnerStates =
                ImmutableSLList.nil();

        // Unify names in join partner symbolic state and path condition
        {
            ImmutableList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> tmpJoinPartners =
                    joinPartners;
            for (final SymbolicExecutionState joinPartnerState : joinRuleApp
                    .getJoinPartnerStates()) {

                final HashMap<ProgramVariable, ProgramVariable> replMap =
                        tmpJoinPartners.head().third;
                final ProgVarReplacer replacer =
                        new ProgVarReplacer(replMap, services);

                ImmutableList<Term> newElementaries = ImmutableSLList.nil();
                final LinkedList<Term> elementaries =
                        JoinRuleUtils.getElementaryUpdates(joinPartnerState
                                .getSymbolicState());
                for (final Term elementary : elementaries) {
                    final ElementaryUpdate upd =
                            (ElementaryUpdate) elementary.op();
                    final LocationVariable lhs =
                            replMap.containsKey((LocationVariable) upd.lhs()) ? (LocationVariable) replMap
                                    .get((LocationVariable) upd.lhs())
                                    : (LocationVariable) upd.lhs();

                    newElementaries =
                            newElementaries.prepend(tb.elementary(
                                    lhs,
                                    elementary.sub(0)));
                }

                joinPartnerStates =
                        joinPartnerStates.prepend(new SymbolicExecutionState(tb
                                .parallel(newElementaries), replacer
                                .replace(joinPartnerState.getPathCondition())));

                tmpJoinPartners = tmpJoinPartners.tail();

            }
        }

        // The join loop
        SymbolicExecutionState joinedState =
                new SymbolicExecutionState(thisSEState.first,
                        thisSEState.second, newGoal.node());
        ImmutableSet<Name> newNames = DefaultImmutableSet.nil();

        for (SymbolicExecutionState state : joinPartnerStates) {
            Pair<SymbolicExecutionState, ImmutableSet<Name>> joinResult =
                    joinStates(joinRule, joinedState, state, thisSEState.third,
                            joinRuleApp.getDistinguishingFormula(), services);
            newNames = newNames.union(joinResult.second);

            joinedState = joinResult.first;
            joinedState.setCorrespondingNode(newGoal.node());
        }

        final Term resultPathCondition = joinedState.second;

        // NOTE (DS): The following simplification has been commented
        // out since it was usually not successful and consumed an
        // inadequate amount of time.
        // final Term previousResultPathCondition = resultPathCondition;
        // resultPathCondition = trySimplify(services.getProof(),
        // resultPathCondition, true);

        // Delete previous sequents
        clearSemisequent(newGoal, true);
        clearSemisequent(newGoal, false);

        newGoal.indexOfTaclets().removeTaclets(
                newGoal.indexOfTaclets().getPartialInstantiatedApps());

        // Add new antecedent (path condition)
        for (Term antecedentFormula : getConjunctiveElementsFor(resultPathCondition)) {
            final SequentFormula newAntecedent =
                    new SequentFormula(antecedentFormula);
            newGoal.addFormula(newAntecedent, true, false);
        }

        // Add new succedent (symbolic state & program counter)
        final Term succedentFormula =
                tb.apply(joinedState.first, thisSEState.third);
        final SequentFormula newSuccedent =
                new SequentFormula(succedentFormula);
        newGoal.addFormula(newSuccedent, new PosInOccurrence(newSuccedent,
                PosInTerm.getTopLevel(), false));

        // The following line has the only effect of emptying the
        // name recorder -- the name recorder for currentNode will
        // be filled after partner node closing. The purpose of this
        // measure is to avoid new names of join nodes being added as
        // new names of the partners.
        services.saveNameRecorder(currentNode);

        // Close partner goals
        for (Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>> joinPartner : joinPartners) {
            closeJoinPartnerGoal(
                    newGoal.node(),
                    joinPartner.first,
                    joinPartner.second,
                    joinedState,
                    sequentToSEPair(joinPartner.first.node(),
                            joinPartner.second, services), thisSEState.third);
        }

        // Register new names
        for (Name newName : newNames) {
            services.addNameProposal(newName);
        }

        return newGoals;
    }
    
    /**
     * Joins two SE states (U1,C1,p) and (U2,C2,p) according to the method
     * {@link JoinRule#joinValuesInStates(LocationVariable, SymbolicExecutionState, Term, SymbolicExecutionState, Term, Services)}
     * . p must be the same in both states, so it is supplied separately.
     * <p>
     * 
     * Override this method for special join procedures.
     *
     * @param joinRule
     *            The join procedure to use for the join.
     * @param state1
     *            First state to join.
     * @param state2
     *            Second state to join.
     * @param programCounter
     *            The formula \&lt;{ ... }\&gt; phi consisting of the common
     *            program counter and the post condition.
     * @param distinguishingFormula
     *            The user-specified distinguishing formula. May be null (for
     *            automatic generation).
     * @param services
     *            The services object.
     * @return A new joined SE state (U*,C*) which is a weakening of the
     *         original states.
     */
    @SuppressWarnings("unused") /* For deactivated equiv check */
    protected Pair<SymbolicExecutionState, ImmutableSet<Name>> joinStates(
            JoinProcedure joinRule, SymbolicExecutionState state1,
            SymbolicExecutionState state2, Term programCounter,
            Term distinguishingFormula, Services services) {

        final TermBuilder tb = services.getTermBuilder();

        // Newly introduced names
        ImmutableSet<Name> newNames = DefaultImmutableSet.nil();

        // Construct path condition as (optimized) disjunction
        Term newPathCondition =
                createSimplifiedDisjunctivePathCondition(state1.second,
                        state2.second, services, SIMPLIFICATION_TIMEOUT_MS);

        ImmutableSet<LocationVariable> progVars = DefaultImmutableSet.nil();

        // Collect program variables in Java block
        progVars =
                progVars.union(getLocationVariables(programCounter, services));
        // Collect program variables in update
        progVars = progVars.union(getUpdateLeftSideLocations(state1.first));
        progVars = progVars.union(getUpdateLeftSideLocations(state2.first));

        ImmutableList<Term> newElementaryUpdates = ImmutableSLList.nil();

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
                    && rightSide2.depth() <= MAX_UPDATE_TERM_DEPTH_FOR_CHECKING
                    && !proofClosed
                    && !JoinRule.RIGHT_SIDE_EQUIVALENCE_ONLY_SYNTACTICAL) {

                Term predicateTerm =
                        tb.func(new Function(new Name("P"), Sort.FORMULA, v
                                .sort()), tb.var(v));
                Term appl1 = tb.apply(state1.first, predicateTerm);
                Term appl2 = tb.apply(state2.first, predicateTerm);
                Term toProve =
                        tb.and(tb.imp(appl1, appl2), tb.imp(appl2, appl1));

                proofClosed =
                        isProvableWithSplitting(toProve, services,
                                SIMPLIFICATION_TIMEOUT_MS);
            }

            if (proofClosed) {

                // Arbitrary choice: Take value of first state if
                // this does not equal the program variable itself
                if (!rightSide1.equals(tb.var(v))) {
                    newElementaryUpdates =
                            newElementaryUpdates.prepend(tb.elementary(v,
                                    rightSide1));
                }

            }
            else {

                // Apply if-then-else construction: Different values

                Sort heapSort =
                        (Sort) services.getNamespaces().sorts().lookup("Heap");

                if (v.sort().equals(heapSort)) {

                    Triple<ImmutableSet<Term>, Term, ImmutableSet<Name>> joinedHeaps =
                            joinHeaps(joinRule, v, rightSide1, rightSide2,
                                    state1, state2, distinguishingFormula, services);
                    newElementaryUpdates =
                            newElementaryUpdates.prepend(tb.elementary(v,
                                    joinedHeaps.second));
                    newPathCondition =
                            tb.and(newPathCondition, tb.and(joinedHeaps.first));
                    newNames = newNames.union(joinedHeaps.third);

                }
                else {

                    Triple<ImmutableSet<Term>, Term, ImmutableSet<Name>> joinedVal =
                            joinRule.joinValuesInStates(tb.var(v), state1,
                                    rightSide1, state2, rightSide2, distinguishingFormula, services);

                    newNames = newNames.union(joinedVal.third);

                    newElementaryUpdates =
                            newElementaryUpdates.prepend(tb.elementary(v,
                                    joinedVal.second));

                    newPathCondition =
                            tb.and(newPathCondition, tb.and(joinedVal.first));

                } // end else of if (v.sort().equals(heapSort))

            } // end else of if (proofClosed)

        } // end for (LocationVariable v : progVars)

        // Construct weakened symbolic state
        Term newSymbolicState = tb.parallel(newElementaryUpdates);

        return new Pair<SymbolicExecutionState, ImmutableSet<Name>>(
                new SymbolicExecutionState(newSymbolicState, newPathCondition),
                newNames);

    }

    /**
     * Joins two heaps in a zip-like procedure. The fallback is an if-then-else
     * construct that is tried to be shifted as far inwards as possible.
     * <p>
     * 
     * Override this method for specialized heap join procedures.
     * 
     * @param heapVar
     *            The heap variable for which the values should be joined.
     * @param heap1
     *            The first heap term.
     * @param heap2
     *            The second heap term.
     * @param state1
     *            SE state for the first heap term.
     * @param state2
     *            SE state for the second heap term
     * @param services
     *            The services object.
     * @param distinguishingFormula
     *            The user-specified distinguishing formula. May be null (for
     *            automatic generation).
     * @return A joined heap term.
     */
    protected Triple<ImmutableSet<Term>, Term, ImmutableSet<Name>> joinHeaps(
            final JoinProcedure joinRule, final LocationVariable heapVar,
            final Term heap1, final Term heap2,
            final SymbolicExecutionState state1,
            final SymbolicExecutionState state2, Term distinguishingFormula,
            final Services services) {

        final TermBuilder tb = services.getTermBuilder();
        ImmutableSet<Term> newConstraints = DefaultImmutableSet.nil();
        ImmutableSet<Name> newNames = DefaultImmutableSet.nil();

        if (heap1.equals(heap2)) {
            // Keep equal heaps
            return new Triple<ImmutableSet<Term>, Term, ImmutableSet<Name>>(
                    newConstraints, heap1, newNames);
        }

        if (!(heap1.op() instanceof Function)
                || !(heap2.op() instanceof Function)) {
            // Covers the case of two different symbolic heaps
            return new Triple<ImmutableSet<Term>, Term, ImmutableSet<Name>>(
                    newConstraints, JoinIfThenElse.createIfThenElseTerm(state1,
                            state2, heap1, heap2, distinguishingFormula, services), newNames);
        }

        final Function storeFunc =
                (Function) services.getNamespaces().functions().lookup("store");
        final Function createFunc =
                (Function) services.getNamespaces().functions()
                        .lookup("create");
        // Note: Check if there are other functions that should be covered.
        // Unknown functions are treated by if-then-else procedure.

        if (((Function) heap1.op()).equals(storeFunc)
                && ((Function) heap2.op()).equals(storeFunc)) {

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

                Triple<ImmutableSet<Term>, Term, ImmutableSet<Name>> joinedSubHeap =
                        joinHeaps(joinRule, heapVar, subHeap1, subHeap2,
                                state1, state2, distinguishingFormula, services);
                newConstraints = newConstraints.union(joinedSubHeap.first);
                newNames = newNames.union(joinedSubHeap.third);

                Term joinedVal = null;

                if (value1.equals(value2)) {
                    // Idempotency...
                    joinedVal = value1;

                }
                else {

                    Triple<ImmutableSet<Term>, Term, ImmutableSet<Name>> joinedValAndConstr =
                            joinRule.joinValuesInStates(field1, state1, value1,
                                    state2, value2, distinguishingFormula, services);

                    newConstraints =
                            newConstraints.union(joinedValAndConstr.first);
                    newNames = newNames.union(joinedValAndConstr.third);
                    joinedVal = joinedValAndConstr.second;

                }

                return new Triple<ImmutableSet<Term>, Term, ImmutableSet<Name>>(
                        newConstraints, tb.func((Function) heap1.op(),
                                joinedSubHeap.second, heap1.sub(1), field1,
                                joinedVal), newNames);

            } // end if (pointer1.equals(pointer2) && field1.equals(field2))

        }
        else if (((Function) heap1.op()).equals(createFunc)
                && ((Function) heap2.op()).equals(createFunc)) {

            // Create operations.

            // Decompose the heap operations.
            Term subHeap1 = heap1.sub(0);
            Term pointer1 = heap1.sub(1);

            Term subHeap2 = heap2.sub(0);
            Term pointer2 = heap2.sub(1);

            if (pointer1.equals(pointer2)) {
                // Same objects are created: Join.

                Triple<ImmutableSet<Term>, Term, ImmutableSet<Name>> joinedSubHeap =
                        joinHeaps(joinRule, heapVar, subHeap1, subHeap2,
                                state1, state2, distinguishingFormula, services);
                newConstraints = newConstraints.union(joinedSubHeap.first);
                newNames = newNames.union(joinedSubHeap.third);

                return new Triple<ImmutableSet<Term>, Term, ImmutableSet<Name>>(
                        newConstraints, tb.func((Function) heap1.op(),
                                joinedSubHeap.second, pointer1), newNames);
            }

            // "else" case is fallback at end of method:
            // if-then-else of heaps.

        } // end else of else if (((Function) heap1.op()).equals(createFunc) &&
          // ((Function) heap2.op()).equals(createFunc))

        return new Triple<ImmutableSet<Term>, Term, ImmutableSet<Name>>(
                newConstraints, JoinIfThenElse.createIfThenElseTerm(state1,
                        state2, heap1, heap2, distinguishingFormula, services), newNames);

    }

    /**
     * We admit top level formulas of the form \&lt;{ ... }\&gt; phi and U
     * \&lt;{ ... }\&gt; phi, where U must be an update in normal form, i.e. a
     * parallel update of elementary updates.
     * 
     * @param goal
     *            Current goal.
     * @param pio
     *            Position of selected sequent formula.
     * @return true iff a suitable top level formula for joining.
     */
    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        // Note: We do not check for join partner existence
        // to save time during automatic execution.
        // As a result, the rule is applicable for any
        // formula of suitable form, but then with empty
        // list of candidates.

        return isOfAdmissibleForm(goal, pio, false); // Don't do the check for
                                                     // partner existence
    }

    /**
     * We admit top level formulas of the form \&lt;{ ... }\&gt; phi and U
     * \&lt;{ ... }\&gt; phi, where U must be an update in normal form, i.e. a
     * parallel update of elementary updates. We require that phi does not
     * contain a Java block.
     * 
     * @param goal
     *            Current goal.
     * @param pio
     *            Position of selected sequent formula.
     * @param doJoinPartnerCheck
     *            Checks for available join partners iff this flag is set to
     *            true.
     * @return true iff a suitable top level formula for joining.
     */
    public static boolean isOfAdmissibleForm(Goal goal, PosInOccurrence pio,
            boolean doJoinPartnerCheck) {
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
            }
            else {
                return false;
            }
        }
        else {
            // NOTE: This disallows joins for formulae without updates
            // in front. In principle, joins are possible for
            // arbitrary formulae, but this significantly slows
            // down the JavaCardDLStrategy since for every formula,
            // all goals in the tree are searched. For the intended
            // applications, it suffices to allow joins just for
            // formulae of the form {U}\phi.
            return false;
        }

        // Term after update must have the form "phi" or "\<{...}\> phi" or
        // "\[{...}\]", where phi must not contain a Java block.
        if (termAfterUpdate.op() instanceof Modality
                && !termAfterUpdate.sub(0).javaBlock()
                        .equals(JavaBlock.EMPTY_JAVABLOCK)) {
            return false;
        }
        else if (termAfterUpdate.op() instanceof UpdateApplication) {
            return false;
        }

        return !doJoinPartnerCheck
                || findPotentialJoinPartners(goal, pio).size() > 0;

    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pio, TermServices services) {
        return new JoinRuleBuiltInRuleApp(this, pio);
    }

    /**
     * Finds all suitable join partners.
     * 
     * @param goal
     *            Current goal to join.
     * @param pio
     *            Position of update-program counter formula in goal.
     * @param services
     *            The services object.
     * @return A list of suitable join partners. May be empty if none exist.
     */
    public static ImmutableList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> findPotentialJoinPartners(
            Goal goal, PosInOccurrence pio) {
        return findPotentialJoinPartners(goal, pio, goal.proof().root());
    }

    /**
     * Finds all suitable join partners below the start node.
     * 
     * @param goal
     *            Current goal to join.
     * @param pio
     *            Position of update-program counter formula in goal.
     * @param start
     *            Node to start the search with.
     * @param services
     *            The services object.
     * @return A list of suitable join partners. May be empty if none exist.
     */
    public static ImmutableList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> findPotentialJoinPartners(
            Goal goal, PosInOccurrence pio, Node start) {

        Services services = goal.proof().getServices();

        ImmutableList<Goal> allGoals =
                services.getProof().getSubtreeGoals(start);

        // Find potential partners -- for which isApplicable is true and
        // they have the same program counter (and post condition).
        ImmutableList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> potentialPartners =
                ImmutableSLList.nil();
        for (Goal g : allGoals) {
            if (!g.equals(goal) && !g.isLinked()) {
                Semisequent succedent = g.sequent().succedent();
                for (int i = 0; i < succedent.size(); i++) {
                    SequentFormula f = succedent.get(i);

                    PosInTerm pit = PosInTerm.getTopLevel();

                    PosInOccurrence gPio = new PosInOccurrence(f, pit, false);
                    if (isOfAdmissibleForm(g, gPio, false)) {
                        Triple<Term, Term, Term> ownSEState =
                                sequentToSETriple(goal.node(), pio, services);
                        Triple<Term, Term, Term> partnerSEState =
                                sequentToSETriple(g.node(), gPio, services);

                        // NOTE: The equality check for the Java blocks can be
                        // problematic, since KeY instantiates declared program
                        // variables with different identifiers; e.g.
                        // {int x = 10; if (x...)} could get
                        // {x_1 = 10; if (x_1...)}
                        // in one and {x_2 = 10; if (x_2...)} in the other
                        // branch. This cannot be circumvented with
                        // equalsModRenaming, since at this point, the PVs are
                        // already declared. We therefore check equality
                        // modulo switching to branch-unique (and not globally
                        // unique) names.
                        // TODO: Update this comment above

                        JavaProgramElement ownProgramElem =
                                ownSEState.third.javaBlock().program();
                        JavaProgramElement partnerProgramElem =
                                partnerSEState.third.javaBlock().program();

                        Term ownPostCond =
                                ownSEState.third.op() instanceof Modality ? ownSEState.third
                                        .sub(0) : ownSEState.third;
                        Term partnerPostCond =
                                partnerSEState.third.op() instanceof Modality ? partnerSEState.third
                                        .sub(0) : partnerSEState.third;

                        ProgramVariablesMatchVisitor matchVisitor =
                                new ProgramVariablesMatchVisitor(
                                        partnerProgramElem, ownProgramElem,
                                        services);
                        matchVisitor.start();

                        // Requirement: Same post condition, matching program
                        // parts.
                        // NOTE: If we have a modality in the post condition,
                        // the equality of post conditions may be too strict,
                        // so some legal cases will be excluded from the join
                        // partners list.
                        if (ownPostCond.equals(partnerPostCond)
                                && !matchVisitor.isIncompatible()) {

                            potentialPartners =
                                    potentialPartners
                                            .prepend(new Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>(
                                                    g, gPio, matchVisitor
                                                            .getMatches()
                                                            .getValue()));

                        }
                    }
                }
            }
        }

        return potentialPartners;
    }

}
