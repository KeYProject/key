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

package de.uka.ilkd.key.rule.join.procedures;

import static de.uka.ilkd.key.util.joinrule.JoinRuleUtils.countAtoms;
import static de.uka.ilkd.key.util.joinrule.JoinRuleUtils.getDistinguishingFormula;
import static de.uka.ilkd.key.util.joinrule.JoinRuleUtils.getUpdateRightSideFor;
import static de.uka.ilkd.key.util.joinrule.JoinRuleUtils.trySimplify;

import java.util.LinkedHashSet;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.rule.join.JoinProcedure;
import de.uka.ilkd.key.rule.join.JoinRule;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Quadruple;
import de.uka.ilkd.key.util.Triple;
import de.uka.ilkd.key.util.joinrule.JoinRuleUtils.Option;
import de.uka.ilkd.key.util.joinrule.SymbolicExecutionState;

/**
 * Rule that joins two sequents based on the if-then-else construction: If two
 * locations are assigned different values in the states, the value in the
 * joined state is chosen based on the path condition. This rule retains total
 * precision. The if-then-else distinction is realized by the respective
 * construct for the update / symbolic state of the symbolic execution state.
 * Note: Doing this not with updates, but in the antecedent / path condition can
 * be much more efficient: See {@link JoinIfThenElseAntecedent}.
 * 
 * @author Dominic Scheurer
 * @see JoinIfThenElseAntecedent
 * @see JoinRule
 */
public class JoinIfThenElse extends JoinProcedure {
    private static JoinIfThenElse INSTANCE = null;
    
    /** Time in milliseconds after which a simplification attempt
     *  of a distinguishing formula times out. */
    private static final int SIMPLIFICATION_TIMEOUT_MS = 1000;

    public static JoinIfThenElse instance() {
        if (INSTANCE == null) {
            INSTANCE = new JoinIfThenElse();
        }
        return INSTANCE;
    }

    private static final String DISPLAY_NAME = "JoinByIfThenElse";
    static final int MAX_UPDATE_TERM_DEPTH_FOR_CHECKING = 8;
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.rule.join.JoinProcedure#complete()
     */
    @Override
    public boolean complete() {
        return true;
    }

    @Override
    public Triple<ImmutableSet<Term>, Term, LinkedHashSet<Name>> joinValuesInStates(
            Term v, SymbolicExecutionState state1,
            Term valueInState1, SymbolicExecutionState state2,
            Term valueInState2, Term distinguishingFormula, Services services) {

        return new Triple<ImmutableSet<Term>, Term, LinkedHashSet<Name>>(
                DefaultImmutableSet.<Term> nil(), createIfThenElseTerm(state1,
                        state2, valueInState1, valueInState2,
                        distinguishingFormula, services),
                new LinkedHashSet<Name>());

    }
    @Override
    public boolean requiresDistinguishablePathConditions() {
        return true;
    }

    /**
     * Creates an if-then-else term for the variable v. If t1 is the right side
     * for v in state1, and t2 is the right side in state1, the resulting term
     * corresponds to <code>\if (c1) \then (t1) \else (t2)</code>, where c1 is
     * the path condition of state1. However, the method also tries an
     * optimization: The path condition c2 of state2 could be used if it is
     * shorter than c1. Moreover, equal parts of c1 and c2 could be omitted,
     * since the condition shall only distinguish between the states.
     * 
     * @param state1
     *            First state to evaluate.
     * @param state2
     *            Second state to evaluate.
     * @param ifTerm
     *            The term t1 (in the context of state1).
     * @param elseTerm
     *            The term t2 (in the context of state2).
     * @param distinguishingFormula
     *            The user-specified distinguishing formula. May be null (for
     *            automatic generation).
     * @param services
     *            The services object.
     * @return An if then else term like
     *         <code>\if (c1) \then (t1) \else (t2)</code>, where the cI are the
     *         path conditions of stateI.
     */
    public static Term createIfThenElseTerm(
            final SymbolicExecutionState state1,
            final SymbolicExecutionState state2, final Term ifTerm,
            final Term elseTerm, Term distinguishingFormula,
            final Services services) {

        TermBuilder tb = services.getTermBuilder();

        Term cond, ifForm, elseForm;
        
        if (distinguishingFormula == null) {
            Quadruple<Term, Term, Term, Boolean> distFormAndRightSidesForITEUpd = createDistFormAndRightSidesForITEUpd(
                        state1, state2, ifTerm, elseTerm, services);
    
            cond = distFormAndRightSidesForITEUpd.first;
            ifForm = distFormAndRightSidesForITEUpd.second;
            elseForm = distFormAndRightSidesForITEUpd.third;
        }
        else {
            cond = distinguishingFormula;
            ifForm = ifTerm;
            elseForm = elseTerm;
        }

        // Construct the update for the symbolic state
        return tb.ife(cond, ifForm, elseForm);

    }

    /**
     * Creates the input for an if-then-else update for the variable v. If t1 is
     * the right side for v in state1, and t2 is the right side in state1, the
     * elements of the resulting quadruple can be used to construct an
     * elementary update corresponding to
     * <code>{ v := \if (c1) \then (t1) \else (t2) }</code>, where c1 is the
     * path condition of state1. However, the method also tries an optimization:
     * The path condition c2 of state2 could be used if it is shorter than c1.
     * Moreover, equal parts of c1 and c2 could be omitted, since the condition
     * shall only distinguish between the states. The first element of the
     * triple is the discriminating condition, the second and third elements are
     * the respective parts for the if and else branch.
     * 
     * @param v
     *            Variable to return the update for.
     * @param state1
     *            First state to evaluate.
     * @param state2
     *            Second state to evaluate.
     * @param services
     *            The services object.
     * @return Input to construct an elementary update like
     *         <code>{ v := \if (first) \then (second) \else (third) }</code>,
     *         where first, second and third are the respective components of
     *         the returned triple. The fourth component indicates whether the
     *         path condition of the first (fourth component = false) or the
     *         second (fourth component = true) state was used as a basis for
     *         the condition (first component).
     */
    static Quadruple<Term, Term, Term, Boolean> createDistFormAndRightSidesForITEUpd(
            LocationVariable v, SymbolicExecutionState state1,
            SymbolicExecutionState state2, Services services) {

        TermBuilder tb = services.getTermBuilder();

        Term rightSide1 = getUpdateRightSideFor(state1.first, v);
        Term rightSide2 = getUpdateRightSideFor(state2.first, v);

        if (rightSide1 == null) {
            rightSide1 = tb.var(v);
        }

        if (rightSide2 == null) {
            rightSide2 = tb.var(v);
        }

        return createDistFormAndRightSidesForITEUpd(state1, state2, rightSide1,
                rightSide2, services);
    }

    /**
     * Creates the input for an if-then-else update. The elements of the
     * resulting quadruple can be used to construct an elementary update
     * corresponding to
     * <code>{ v := \if (c1) \then (ifTerm) \else (elseTerm) }</code>, where c1
     * is the path condition of state1. However, the method also tries an
     * optimization: The path condition c2 of state2 could be used if it is
     * shorter than c1. Moreover, equal parts of c1 and c2 could be omitted,
     * since the condition shall only distinguish between the states. The first
     * element of the triple is the discriminating condition, the second and
     * third elements are the respective parts for the if and else branch.
     * 
     * @param state1
     *            First state to evaluate.
     * @param state2
     *            Second state to evaluate.
     * @param ifTerm
     *            The if term.
     * @param elseTerm
     *            The else term.
     * @param services
     *            The services object.
     * @return Input to construct an elementary update like
     *         <code>{ v := \if (first) \then (second) \else (third) }</code>,
     *         where first, second and third are the respective components of
     *         the returned triple. The fourth component indicates whether the
     *         path condition of the first (fourth component = false) or the
     *         second (fourth component = true) state was used as a basis for
     *         the condition (first component).
     */
    static Quadruple<Term, Term, Term, Boolean> createDistFormAndRightSidesForITEUpd(
            SymbolicExecutionState state1, SymbolicExecutionState state2,
            Term ifTerm, Term elseTerm, Services services) {

        // We only need the distinguishing subformula; the equal part
        // is not needed. For soundness, it suffices that the "distinguishing"
        // formula is implied by the original path condition; for completeness,
        // we add the common subformula in the new path condition, if it
        // is not already implied by that.
        Option<Pair<Term, Term>> distinguishingAndEqualFormula1 = getDistinguishingFormula(
                state1.second, state2.second, services);
        Term distinguishingFormula = distinguishingAndEqualFormula1.isSome() ? distinguishingAndEqualFormula1
                .getValue().first : null;

        Option<Pair<Term, Term>> distinguishingAndEqualFormula2 = getDistinguishingFormula(
                state2.second, state1.second, services);
        Term distinguishingFormula2 = distinguishingAndEqualFormula2.isSome() ? distinguishingAndEqualFormula2
                .getValue().first : null;

        // NOTE (DS): This assertion does not prevent the joining of states with equal
        // Symbolic State. This is intended behavior: In some proofs we have two identical
        // nodes which we want to join (possibly after a hide right / hide left); this
        // should be allowed (although they are of course indistinguishable).
        assert distinguishingFormula != null || distinguishingFormula2 != null : String
                .format("\nA computed distinguishing formula is trivial (\"true\"); "
                        + "please verify that everything is OK. Symbolic execution states were:\n\n"
                        + "--- State 1 ---\n%s\n\n---State 2---\n%s\n", state1,
                        state2);

        boolean commuteSides = false;
        if (distinguishingFormula == null) {
            distinguishingFormula = distinguishingFormula2;
            commuteSides = true;
        }
        else if (distinguishingFormula2 != null) {
            // Choose the shorter distinguishing formula
            if (countAtoms(distinguishingFormula2) < countAtoms(distinguishingFormula)) {
                distinguishingFormula = distinguishingFormula2;
                commuteSides = true;
            }
        }

        // Try an automatic simplification
        distinguishingFormula = trySimplify(services.getProof(),
                distinguishingFormula, true, SIMPLIFICATION_TIMEOUT_MS);

        // Originally, here was a specific check of whether the equal parts
        // of the two path conditions was still included in the new path
        // condition.
        // However, this should always be the case; it shouldn't vanish in
        // the creation of the disjunction. Even if it did, soundness would
        // not be affected, it only could be a completeness issue. Uncomment
        // the code below if you want to test this measure.

        /*
         * Term equalSubFormula = distinguishingAndEqualFormula1.second; // Add
         * common subformula to path condition, if necessary Term
         * commonPartAlreadyImpliedForm = tb.imp(newPathCondition,
         * equalSubFormula); if
         * (!isProvableWithSplitting(commonPartAlreadyImpliedForm, services)) {
         * newPathCondition = tb.and(newPathCondition, equalSubFormula); }
         */

        return new Quadruple<Term, Term, Term, Boolean>(distinguishingFormula,
                commuteSides ? elseTerm : ifTerm, commuteSides ? ifTerm
                        : elseTerm, commuteSides);

    }

    @Override
    public String toString() {
        return DISPLAY_NAME;
    }
}
