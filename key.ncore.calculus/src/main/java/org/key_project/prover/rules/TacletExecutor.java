/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules;

import java.util.Iterator;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Term;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.instantiation.AssumesFormulaInstSeq;
import org.key_project.prover.rules.instantiation.AssumesFormulaInstantiation;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.instantiation.SVInstantiations;
import org.key_project.prover.sequent.*;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public abstract class TacletExecutor<Goal extends @NonNull ProofGoal<Goal>, App extends @NonNull RuleApp>
        implements RuleExecutor<Goal> {

    protected static final String AUTO_NAME = "_taclet";

    protected final Taclet taclet;

    protected TacletExecutor(Taclet taclet) {
        this.taclet = taclet;
    }

    /// Search for formulas within p_list that have to be proved by an explicit assumes-goal, i.e.
    /// elements of type [AssumesFormulaInstantiation].
    ///
    /// @param p_goal the [Goal] on which the taclet is applied
    /// @param p_list the list of [AssumesFormulaInstantiation] containing the instantiations
    /// for the assumes formulas
    /// @param p_matchCond the [MatchConditions] with the instantiations of the schema
    /// variables
    /// @param p_numberOfNewGoals the number of new goals the [Taclet] creates in any case
    /// because of existing [TacletGoalTemplate]s
    /// @return a list with the original sequent if no such formulas existed, otherwise the list has
    /// two entries: one for the original sequent and one with the sequent encoding the proof
    /// obligation for the to be proven formulas of the assumes goal
    protected ImmutableList<SequentChangeInfo> checkAssumesGoals(Goal p_goal,
            ImmutableList<? extends AssumesFormulaInstantiation> p_list,
            MatchResultInfo p_matchCond,
            int p_numberOfNewGoals) {
        ImmutableList<SequentChangeInfo> res = null;
        Iterator<SequentChangeInfo> itNewGoalSequents;

        // proof obligation for the assumes-formulas
        Term assumesObl = null;

        // always create at least one new goal
        if (p_numberOfNewGoals == 0) {
            p_numberOfNewGoals = 1;
        }

        if (p_list != null) {
            int i = taclet.assumesSequent().antecedent().size();
            Term assumesPart;

            for (final AssumesFormulaInstantiation inst : p_list) {
                if (!(inst instanceof AssumesFormulaInstSeq)) {
                    // build the assumes-obligation formula
                    assumesPart = inst.getSequentFormula().formula();

                    // negate formulas of the assumes-succedent
                    if (i <= 0) {
                        assumesPart = not(assumesPart, p_goal);
                    }

                    if (res == null) {
                        res = ImmutableSLList.nil();
                        for (int j = 0; j < p_numberOfNewGoals + 1; j++) {
                            // noinspection unchecked
                            res = res.prepend(
                                SequentChangeInfo.createSequentChangeInfo(p_goal.sequent()));
                        }
                        assumesObl = assumesPart;
                    } else {
                        // noinspection unchecked
                        assert assumesObl != null
                                : "@AssumeAssertion(nullness): assumesObl should not be null";
                        assumesObl = and(assumesObl, assumesPart, p_goal);
                    }

                    // UGLY: We create a flat structure of the new
                    // goals, thus the `assumes` formulas have to be added to
                    // every new goal
                    itNewGoalSequents = res.iterator();
                    SequentChangeInfo seq = itNewGoalSequents.next();
                    while (itNewGoalSequents.hasNext()) {
                        // (i > 0) iff inst is formula of the antecedent
                        addToPosWithoutInst(inst.getSequentFormula(), seq, null, (i > 0));
                        seq = itNewGoalSequents.next();
                    }
                }

                --i;
            }
        }

        if (res == null) {
            res = ImmutableSLList.nil();
            for (int j = 0; j < p_numberOfNewGoals; j++) {
                // noinspection unchecked
                res = res.prepend(SequentChangeInfo.createSequentChangeInfo(p_goal.sequent()));
            }
        } else {
            // find the sequent the `assumes` obligation has to be added to
            itNewGoalSequents = res.iterator();
            SequentChangeInfo seq = itNewGoalSequents.next();
            while (itNewGoalSequents.hasNext()) {
                seq = itNewGoalSequents.next();
            }
            assert assumesObl != null : "@AssumeAssertion(nullness): assumesObl should not be null";
            addToPosWithoutInst(createSequentFormula(assumesObl), seq, null, false);
        }

        return res;
    }

    protected @NonNull SequentFormula createSequentFormula(@NonNull Term form) {
        return new SequentFormula(form);
    }

    protected abstract Term not(Term t, Goal goal);

    protected abstract Term and(Term t1, Term t2, Goal p_goal);

    /// adds the given SequentFormula to antecedent or succedent depending on position information
    /// or the boolean `addToAntecedent` contrary to "addToPos" the formula `frm` will
    /// not be modified
    ///
    /// @param frm the [SequentFormula] that should be added
    /// @param currentSequent the [SequentChangeInfo] which is the current (intermediate)
    /// result of applying the taclet
    /// @param pos the [PosInOccurrence] describing the place in the sequent
    /// @param addToAntecedent boolean true(false) if elements have to be added to the
    /// antecedent(succedent) (only looked at if `pos == null`)
    private void addToPosWithoutInst(@NonNull SequentFormula frm, SequentChangeInfo currentSequent,
            @Nullable PosInOccurrence pos, boolean addToAntecedent) {
        if (pos != null) {
            currentSequent.combine(currentSequent.sequent().addFormula(frm, pos));
        } else {
            // cf : formula to be added , 1. true/false: addToAntecedent/succ,
            // 2. true: at head
            currentSequent.combine(currentSequent.sequent().addFormula(frm, addToAntecedent, true));
        }
    }

    ///
    /// adds the given rules (i.e. the rules to add according to the Taclet goal template to the
    /// node
    /// of the given goal)
    ///
    /// @param rules the rules to be added
    /// @param goal the {@link Goal} describing the node where the rules should be added
    /// @param services the {@link LogicServices} encapsulating all logic and program information
    /// @param matchCond the {@link MatchResultInfo} containing in particular the instantiations of
    /// the schemavariables
    protected abstract void applyAddrule(ImmutableList<? extends Taclet> rules, Goal goal,
            LogicServices services,
            MatchResultInfo matchCond);

    protected abstract void applyAddProgVars(ImmutableSet<SchemaVariable> pvs,
            SequentChangeInfo currentSequent, Goal goal, PosInOccurrence posOfFind,
            LogicServices services, MatchResultInfo matchCond);

    /// adds SequentFormula to antecedent depending on position information (if none is handed over
    /// it is added at the head of the antecedent). Of course, it has to be ensured that the
    /// position
    /// information describes one occurrence in the antecedent of the sequent.
    ///
    /// @param semi the [Semisequent] with the [SequentFormula]s to be added
    /// @param currentSequent the [SequentChangeInfo] which represent [Sequent] the
    /// current (intermediate) result of applying the taclet
    /// @param pos the [PosInOccurrence] describing the place in the sequent or null for head
    /// of antecedent
    /// @param applicationPosInOccurrence The [PosInOccurrence] of the [Term] which is
    /// rewritten
    /// @param matchCond the [MatchResultInfo] containing in particular the instantiations of
    /// the SchemaVariables
    /// @param services the [LogicServices] encapsulating all logic and program information
    protected void addToAntec(Semisequent semi, SequentChangeInfo currentSequent,
            PosInOccurrence pos,
            PosInOccurrence applicationPosInOccurrence, MatchResultInfo matchCond, Goal goal,
            App tacletApp, LogicServices services, Object... instantiationInfo) {
        addToPos(semi, currentSequent, pos, applicationPosInOccurrence, true,
            matchCond, goal, tacletApp, services, instantiationInfo);
    }

    /// adds SequentFormula to succedent depending on position information (if none is handed over
    /// it
    /// is added at the head of the succedent). Of course, it has to be ensured that the position
    /// information describes one occurrence in the succedent of the sequent.
    ///
    /// @param semi the [Semisequent] with the [SequentFormula]s to be added
    /// @param pos the [PosInOccurrence] describing the place in the sequent or null for head
    /// of antecedent
    /// @param applicationPosInOccurrence The [PosInOccurrence] of the [Term] which is
    /// rewritten
    /// @param matchCond the [MatchResultInfo] containing in particular the instantiations of
    /// the schemavariables
    /// @param goal the [Goal] that knows the node the formulae have to be added
    /// @param services the [LogicServices] encapsulating all logic information
    protected void addToSucc(Semisequent semi, SequentChangeInfo currentSequent,
            PosInOccurrence pos,
            PosInOccurrence applicationPosInOccurrence, MatchResultInfo matchCond, Goal goal,
            App ruleApp, LogicServices services, Object... instantiationInfo) {
        addToPos(semi, currentSequent, pos, applicationPosInOccurrence, false,
            matchCond, goal, ruleApp, services, instantiationInfo);
    }

    /// Replaces the formula at the given position with the first formula in the given
    /// semisequent and adds possible other formulas of the semisequent starting at the position.
    ///
    /// @param semi the [Semisequent] with the [SequentFormula]s to be added
    /// @param currentSequent the [SequentChangeInfo] which represent [Sequent] the
    /// current (intermediate) result of applying the taclet
    /// @param pos the [PosInOccurrence] describing the place in the sequent
    /// @param matchCond the [MatchResultInfo] containing in particular
    /// @param services the [LogicServices] encapsulating all logic and program information
    protected void replaceAtPos(Semisequent semi,
            SequentChangeInfo currentSequent, PosInOccurrence pos, MatchResultInfo matchCond,
            Goal goal, App ruleApp, LogicServices services, Object... instantiationInfo) {
        if (!semi.isEmpty()) {
            final ImmutableList<SequentFormula> replacements =
                instantiateSemisequent(semi, pos, matchCond, goal, ruleApp, services,
                    instantiationInfo);
            currentSequent.combine(currentSequent.sequent().changeFormula(replacements, pos));
        } else {
            currentSequent.combine(currentSequent.sequent().removeFormula(pos));
        }
    }

    /// instantiates the formulas of semisequent <code>semi</code> and adds the
    /// instantiated formulas at the specified position to <code>goal</code>
    ///
    /// @param semi the Semisequent with the [SequentFormula]s to be added
    /// @param currentSequent the [SequentChangeInfo] which represent [Sequent] the
    /// current (intermediate)
    /// result of applying the taclet
    /// @param pos the [PosInOccurrence] describing the place in the sequent
    /// @param applicationPosInOccurrence The [PosInOccurrence] of the [Term] which is
    /// rewritten
    /// @param antec boolean true(false) if elements have to be added to the antecedent(succedent)
    /// (only looked at if `pos == null`)
    /// @param matchCond the [MatchResultInfo] containing in particular
    /// @param services the [LogicServices] encapsulating all logic and program information
    /// @param instantiationInfo additional instantiation information concerning label:
    protected void addToPos(Semisequent semi,
            SequentChangeInfo currentSequent,
            PosInOccurrence pos,
            PosInOccurrence applicationPosInOccurrence, boolean antec,
            MatchResultInfo matchCond, Goal goal, App tacletApp,
            LogicServices services,
            Object... instantiationInfo) {
        final ImmutableList<SequentFormula> replacements =
            instantiateSemisequent(semi, applicationPosInOccurrence,
                matchCond, goal, tacletApp, services, instantiationInfo);
        if (pos != null) {
            currentSequent.combine(currentSequent.sequent().addFormula(replacements, pos));
        } else {
            currentSequent.combine(currentSequent.sequent().addFormula(replacements, antec, true));
        }
    }

    /// The given formula is instantiated and then the result (usually a complete
    /// instantiated formula) is returned.
    ///
    /// @param schemaFormula the SequentFormula to be instantiated
    /// @param services the LogicServices object carrying ja related information
    /// @param matchCond the MatchConditions object with the instantiations of the schemavariables,
    /// constraints etc.
    /// @param applicationPosInOccurrence The [PosInOccurrence] of the [Term] which is
    /// rewritten
    /// @return the as far as possible instantiated SequentFormula
    protected SequentFormula instantiateReplacement(
            SequentFormula schemaFormula, LogicServices services, MatchResultInfo matchCond,
            PosInOccurrence applicationPosInOccurrence, Goal goal,
            App tacletApp, Object... instantiationInfo) {
        final SVInstantiations svInst = matchCond.getInstantiations();

        Term instantiatedFormula = syntacticalReplace(schemaFormula.formula(),
            applicationPosInOccurrence, matchCond,
            goal, tacletApp, services, instantiationInfo);

        instantiatedFormula = applyContextUpdate(svInst, instantiatedFormula, goal);

        return createSequentFormula(instantiatedFormula);
    }

    protected abstract Term applyContextUpdate(SVInstantiations svInst, Term formula, Goal goal);

    /// a new term is created by replacing variables of term whose replacement is found in the given
    /// SVInstantiations
    ///
    /// @param term the [Term] the syntactical replacement is performed on
    /// @param applicationPosInOccurrence the [PosInOccurrence] of the find term in the sequent
    /// this taclet is applied to
    /// @param mc the [MatchResultInfo] with all instantiations and the constraint
    /// @param goal the [Goal] on which this taclet is applied
    /// @param ruleApp the [RuleApp] with application information
    /// @param services the [LogicServices] with the logic and program model information
    /// @return the (partially) instantiated term
    protected abstract Term syntacticalReplace(Term term,
            PosInOccurrence applicationPosInOccurrence,
            MatchResultInfo mc, Goal goal, App ruleApp, LogicServices services, Object... args);

    /// instantiates the given semisequent with the instantiations found in the match results
    ///
    /// @param semi the [Semisequent] to be instantiated
    /// @param applicationPosInOccurrence The [PosInOccurrence] of the [Term] which is
    /// rewritten
    /// @param matchCond the [MatchResultInfo] including the mapping [SchemaVariable]s to
    /// concrete logic elements
    /// @param services the [LogicServices] with the logic and program model information
    /// @return the instantiated formulas of the semisequent as list
    protected ImmutableList<SequentFormula> instantiateSemisequent(Semisequent semi,
            PosInOccurrence applicationPosInOccurrence, MatchResultInfo matchCond, Goal goal,
            App tacletApp, LogicServices services, Object... instantiationInfo) {
        ImmutableList<SequentFormula> replacements = ImmutableSLList.nil();

        for (final SequentFormula sf : semi) {
            replacements = replacements.append(instantiateReplacement(sf, services,
                matchCond, applicationPosInOccurrence, goal, tacletApp, instantiationInfo));
        }

        return replacements;
    }
}
