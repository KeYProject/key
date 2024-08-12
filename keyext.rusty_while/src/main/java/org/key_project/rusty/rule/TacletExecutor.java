/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import java.util.Iterator;

import org.key_project.logic.Term;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.*;
import org.key_project.rusty.logic.op.Junctor;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.rusty.proof.Goal;
import org.key_project.rusty.proof.Node;
import org.key_project.rusty.rule.inst.GenericSortCondition;
import org.key_project.rusty.rule.inst.SVInstantiations;
import org.key_project.rusty.rule.tacletbuilder.TacletGoalTemplate;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

public abstract class TacletExecutor<T extends Taclet> {
    private static final String AUTO_NAME = "_taclet";

    protected final T taclet;

    public TacletExecutor(T taclet) {
        this.taclet = taclet;
    }

    /**
     * applies the given rule application to the specified goal
     *
     * @param goal the goal that the rule application should refer to.
     * @param services the Services encapsulating all java information
     * @param ruleApp the rule application that is executed.
     * @return List of the goals created by the rule which have to be proved. If this is a
     *         close-goal-taclet ( this.closeGoal () ), the first goal of the return list is the
     *         goal that should be closed (with the constraint this taclet is applied under).
     */
    public abstract ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp);

    /**
     * Search for formulas within p_list that have to be proved by an explicit assumes-goal, i.e.
     * elements of type IfFormulaInstDirect.
     *
     * @param p_goal the {@link Goal} on which the taclet is applied
     * @param p_list the list of {@link IfFormulaInstantiation} containing the instantiations for
     *        the assumes formulas
     * @param p_matchCond the {@link MatchConditions} with the instantiations of the schema
     *        variables
     * @param p_numberOfNewGoals the number of new goals the {@link Taclet} creates in any case
     *        because of existing {@link TacletGoalTemplate}s
     * @return a list with the original sequent if no such formulas existed, otherwise the list has
     *         two entries: one for the original sequent and one with the sequent encoding the proof
     *         obligation for the to be proven formulas of the assumes goal
     */
    protected ImmutableList<SequentChangeInfo> checkIfGoals(Goal p_goal,
            ImmutableList<IfFormulaInstantiation> p_list, MatchConditions p_matchCond,
            int p_numberOfNewGoals) {
        ImmutableList<SequentChangeInfo> res = null;
        Iterator<SequentChangeInfo> itNewGoalSequents;

        // proof obligation for the if-formulas
        Term ifObl = null;

        // always create at least one new goal
        if (p_numberOfNewGoals == 0) {
            p_numberOfNewGoals = 1;
        }

        if (p_list != null) {
            int i = taclet.ifSequent().antecedent().size();
            Term ifPart;

            for (final IfFormulaInstantiation inst : p_list) {
                if (!(inst instanceof IfFormulaInstSeq)) {
                    // build the if obligation formula
                    ifPart = inst.getConstrainedFormula().formula();

                    // negate formulas of the if-succedent
                    final Services services = p_goal.proof().getServices();
                    if (i <= 0) {
                        ifPart = services.getTermBuilder().not(ifPart);
                    }

                    if (res == null) {
                        res = ImmutableSLList.nil();
                        for (int j = 0; j < p_numberOfNewGoals + 1; j++) {
                            res = res.prepend(SequentChangeInfo.createSequentChangeInfo(
                                (SemisequentChangeInfo) null, null,
                                p_goal.sequent(), p_goal.sequent()));
                        }
                        ifObl = ifPart;
                    } else {
                        ifObl = services.getTermFactory().createTerm(Junctor.AND, ifObl, ifPart);
                    }

                    // UGLY: We create a flat structure of the new
                    // goals, thus the if formulas have to be added to
                    // every new goal
                    itNewGoalSequents = res.iterator();
                    SequentChangeInfo seq = itNewGoalSequents.next();
                    while (itNewGoalSequents.hasNext()) {
                        // (i > 0) iff inst is formula of the antecedent
                        addToPosWithoutInst(inst.getConstrainedFormula(), seq, null, (i > 0));
                        seq = itNewGoalSequents.next();
                    }
                }

                --i;
            }
        }

        if (res == null) {
            res = ImmutableSLList.nil();
            for (int j = 0; j < p_numberOfNewGoals; j++) {
                res = res.prepend(
                    SequentChangeInfo.createSequentChangeInfo((SemisequentChangeInfo) null,
                        null, p_goal.sequent(), p_goal.sequent()));
            }
        } else {
            // find the sequent the if obligation has to be added to
            itNewGoalSequents = res.iterator();
            SequentChangeInfo seq = itNewGoalSequents.next();
            while (itNewGoalSequents.hasNext()) {
                seq = itNewGoalSequents.next();
            }

            addToPosWithoutInst(new SequentFormula(ifObl), seq, null, false);
        }

        return res;
    }

    /**
     * adds SequentFormula to antecedent or succedent depending on position information or the
     * boolean antec contrary to "addToPos" frm will not be modified
     *
     * @param frm the {@link SequentFormula} that should be added
     * @param currentSequent the {@link SequentChangeInfo} which is the current (intermediate)
     *        result of applying the taclet
     * @param pos the {@link PosInOccurrence} describing the place in the sequent
     * @param antec boolean true(false) if elements have to be added to the antecedent(succedent)
     *        (only looked at if pos == null)
     */
    private void addToPosWithoutInst(SequentFormula frm, SequentChangeInfo currentSequent,
            PosInOccurrence pos, boolean antec) {
        if (pos != null) {
            currentSequent.combine(currentSequent.sequent().addFormula(frm, pos));
        } else {
            // cf : formula to be added , 1. true/false: antec/succ,
            // 2. true: at head
            currentSequent.combine(currentSequent.sequent().addFormula(frm, antec, true));
        }
    }

    /**
     * adds the given rules (i.e. the rules to add according to the Taclet goal template to the node
     * of the given goal)
     *
     * @param rules the rules to be added
     * @param goal the goal describing the node where the rules should be added
     * @param services the Services encapsulating all java information
     * @param matchCond the MatchConditions containing in particular the instantiations of the
     *        schemavariables
     */
    protected void applyAddrule(ImmutableList<Taclet> rules, Goal goal, Services services,
            MatchConditions matchCond) {

        for (Taclet tacletToAdd : rules) {
            final Node n = goal.getNode();
            tacletToAdd = tacletToAdd
                    .setName(tacletToAdd.name() + AUTO_NAME + n.getUniqueTacletId());


            // the new Taclet may contain variables with a known
            // instantiation. These must be used by the new Taclet and all
            // further rules it contains in the addrules-sections. Therefore all
            // appearing (including the addrules) SchemaVariables have to be
            // collected, then it is looked if an instantiation is known and if
            // positive the instantiation is memorized. At last the Taclet with
            // its required instantiations is handed over to the goal, where a
            // new TacletApp should be built including the necessary instantiation
            // information

            SVInstantiations neededInstances = SVInstantiations.EMPTY_SVINSTANTIATIONS
                    .addUpdateList(matchCond.getInstantiations().getUpdateContext());

            final TacletSchemaVariableCollector collector = new TacletSchemaVariableCollector();
            collector.visit(tacletToAdd, true);// true, because
            // descend into addrules
            for (SchemaVariable sv : collector.vars()) {
                if (matchCond.getInstantiations().isInstantiated(sv)) {
                    neededInstances = neededInstances.add(sv,
                        matchCond.getInstantiations().getInstantiationEntry(sv), services);
                }
            }

            final ImmutableList<GenericSortCondition> cs =
                matchCond.getInstantiations().getGenericSortInstantiations().toConditions();

            for (final GenericSortCondition gsc : cs) {
                neededInstances = neededInstances.add(gsc, services);
            }

            goal.addTaclet(tacletToAdd, neededInstances, true);
        }
    }

    protected void applyAddProgVars(ImmutableSet<SchemaVariable> pvs,
            SequentChangeInfo currentSequent, Goal goal, PosInOccurrence posOfFind,
            Services services, MatchConditions matchCond) {
        // TODO @ DD
    }

    /**
     * adds SequentFormula to antecedent depending on position information (if none is handed over
     * it is added at the head of the antecedent). Of course it has to be ensured that the position
     * information describes one occurrence in the antecedent of the sequent.
     *
     * @param semi the Semisequent with the the ConstrainedFormulae to be added
     * @param currentSequent the Sequent which is the current (intermediate) result of applying the
     *        taclet
     * @param pos the PosInOccurrence describing the place in the sequent or null for head of
     *        antecedent
     * @param applicationPosInOccurrence The {@link PosInOccurrence} of the {@link Term} which is
     *        rewritten
     * @param matchCond the MatchConditions containing in particular the instantiations of the
     *        schemavariables
     * @param services the Services encapsulating all java information
     */
    protected void addToAntec(Semisequent semi, SequentChangeInfo currentSequent,
            PosInOccurrence pos,
            PosInOccurrence applicationPosInOccurrence, MatchConditions matchCond, Goal goal,
            RuleApp tacletApp, Services services) {
        addToPos(semi, currentSequent, pos, applicationPosInOccurrence, true,
            matchCond, goal, services, tacletApp);
    }

    /**
     * adds SequentFormula to succedent depending on position information (if none is handed over it
     * is added at the head of the succedent). Of course it has to be ensured that the position
     * information describes one occurrence in the succedent of the sequent.
     *
     * @param semi the Semisequent with the the ConstrainedFormulae to be added
     * @param pos the PosInOccurrence describing the place in the sequent or null for head of
     *        antecedent
     * @param applicationPosInOccurrence The {@link PosInOccurrence} of the {@link Term} which is
     *        rewritten
     * @param matchCond the MatchConditions containing in particular the instantiations of the
     *        schemavariables
     * @param goal the Goal that knows the node the formulae have to be added
     * @param services the Services encapsulating all java information
     */
    protected void addToSucc(Semisequent semi, SequentChangeInfo currentSequent,
            PosInOccurrence pos,
            PosInOccurrence applicationPosInOccurrence, MatchConditions matchCond, Goal goal,
            RuleApp ruleApp, Services services) {
        addToPos(semi, currentSequent, pos, applicationPosInOccurrence, false,
            matchCond, goal, services, ruleApp);
    }

    /**
     * replaces the constrained formula at the given position with the first formula in the given
     * semisequent and adds possible other formulas of the semisequent starting at the position
     *
     * @param semi the Semisequent with the the ConstrainedFormulae to be added
     * @param currentSequent the Sequent which is the current (intermediate) result of applying the
     *        taclet
     * @param pos the PosInOccurrence describing the place in the sequent
     * @param matchCond the MatchConditions containing in particular
     * @param services the Services encapsulating all java information
     */
    protected void replaceAtPos(Semisequent semi,
            SequentChangeInfo currentSequent, PosInOccurrence pos, MatchConditions matchCond,
            Goal goal, RuleApp ruleApp, Services services) {
        final ImmutableList<SequentFormula> replacements = instantiateSemisequent(semi,
            pos, matchCond, goal, ruleApp, services);
        currentSequent.combine(currentSequent.sequent().changeFormula(replacements, pos));
    }

    /**
     * instantiates the constrained formulas of semisequent <code>semi</code> and adds the
     * instantiatied formulas at the specified position to <code>goal</code>
     *
     * @param semi the Semisequent with the the ConstrainedFormulae to be added
     * @param currentSequent the Sequent which is the current (intermediate) result of applying the
     *        taclet
     * @param pos the PosInOccurrence describing the place in the sequent
     * @param applicationPosInOccurrence The {@link PosInOccurrence} of the {@link Term} which is
     *        rewritten
     * @param antec boolean true(false) if elements have to be added to the antecedent(succedent)
     *        (only looked at if pos == null)
     * @param matchCond the MatchConditions containing in particular
     * @param services the Services encapsulating all java information
     */
    private void addToPos(Semisequent semi, SequentChangeInfo currentSequent, PosInOccurrence pos,
            PosInOccurrence applicationPosInOccurrence, boolean antec,
            MatchConditions matchCond, Goal goal, Services services, RuleApp tacletApp) {

        final ImmutableList<SequentFormula> replacements =
            instantiateSemisequent(semi, applicationPosInOccurrence,
                matchCond, goal, tacletApp, services);
        if (pos != null) {
            currentSequent.combine(currentSequent.sequent().addFormula(replacements, pos));
        } else {
            currentSequent.combine(currentSequent.sequent().addFormula(replacements, antec, true));
        }
    }

    /**
     * the given constrained formula is instantiated and then the result (usually a complete
     * instantiated formula) is returned.
     *
     * @param schemaFormula the SequentFormula to be instantiated
     * @param services the Services object carrying ja related information
     * @param matchCond the MatchConditions object with the instantiations of the schemavariables,
     *        constraints etc.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} of the {@link Term} which is
     *        rewritten
     * @return the as far as possible instantiated SequentFormula
     */
    private SequentFormula instantiateReplacement(
            SequentFormula schemaFormula, Services services, MatchConditions matchCond,
            PosInOccurrence applicationPosInOccurrence, Goal goal,
            RuleApp tacletApp) {

        final SVInstantiations svInst = matchCond.getInstantiations();

        Term instantiatedFormula = syntacticalReplace(schemaFormula.formula(),
            applicationPosInOccurrence, matchCond,
            goal, tacletApp, services);

        if (!svInst.getUpdateContext().isEmpty()) {
            instantiatedFormula = services.getTermBuilder()
                    .applyUpdatePairsSequential(svInst.getUpdateContext(), instantiatedFormula);
        }

        return new SequentFormula(instantiatedFormula);
    }

    /**
     * a new term is created by replacing variables of term whose replacement is found in the given
     * SVInstantiations
     *
     * @param term the {@link Term} the syntactical replacement is performed on
     * @param applicationPosInOccurrence the {@link PosInOccurrence} of the find term in the sequent
     *        this taclet is applied to
     * @param mc the {@link MatchConditions} with all instantiations and the constraint
     * @param goal the {@link Goal} on which this taclet is applied
     * @param ruleApp the {@link RuleApp} with application information
     * @param services the {@link Services} with the Java model information
     * @return the (partially) instantiated term
     */
    protected Term syntacticalReplace(Term term, PosInOccurrence applicationPosInOccurrence,
            MatchConditions mc, Goal goal, RuleApp ruleApp, Services services) {
        final SyntacticalReplaceVisitor srVisitor =
            new SyntacticalReplaceVisitor(applicationPosInOccurrence,
                mc.getInstantiations(), goal, taclet, ruleApp, services);
        term.execPostOrder(srVisitor);
        return srVisitor.getTerm();
    }

    /**
     * instantiates the given semisequent with the instantiations found in Matchconditions
     *
     * @param semi the Semisequent to be instantiated
     * @param applicationPosInOccurrence The {@link PosInOccurrence} of the {@link Term} which is
     *        rewritten
     * @param matchCond the MatchConditions including the mapping Schemavariables to concrete logic
     *        elements
     * @param services the Services
     * @return the instantiated formulas of the semisequent as list
     */
    protected ImmutableList<SequentFormula> instantiateSemisequent(Semisequent semi,

            PosInOccurrence applicationPosInOccurrence, MatchConditions matchCond, Goal goal,
            RuleApp tacletApp, Services services) {

        ImmutableList<SequentFormula> replacements = ImmutableSLList.nil();

        for (SequentFormula sf : semi) {
            replacements = replacements.append(instantiateReplacement(sf, services,
                matchCond, applicationPosInOccurrence, goal, tacletApp));
        }

        return replacements;
    }
}
