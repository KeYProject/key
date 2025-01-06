/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Term;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentChangeInfo;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.rusty.proof.Goal;
import org.key_project.rusty.proof.Node;
import org.key_project.rusty.rule.inst.GenericSortCondition;
import org.key_project.rusty.rule.inst.SVInstantiations;
import org.key_project.util.collection.ImmutableList;

import org.checkerframework.checker.nullness.qual.NonNull;
import org.key_project.util.collection.ImmutableSet;

public abstract class TacletExecutor<T extends Taclet> extends
        org.key_project.prover.rules.TacletExecutor<@NonNull Goal, @NonNull RuleApp, @NonNull T> {
    public TacletExecutor(T taclet) {
        super(taclet);
    }

    @Override
    protected Term not(Term t, @NonNull Goal goal) {
        return goal.getOverlayServices().getTermBuilder().not(t);
    }

    @Override
    protected Term and(Term t1, Term t2, @NonNull Goal goal) {
        return goal.getOverlayServices().getTermBuilder().and(t1, t2);
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
     * @param services the {@link Services} with the Rust model information
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

    @Override
    protected Term syntacticalReplace(Term term, PosInOccurrence applicationPosInOccurrence,
                                      org.key_project.prover.rules.MatchConditions mc, @NonNull Goal goal,
                                      @NonNull RuleApp ruleApp, LogicServices services, Object... instantiationInfo) {
        return syntacticalReplace(term, applicationPosInOccurrence, (MatchConditions) mc, goal,
                ruleApp, (Services) services);
    }

    /**
     * adds the given rules (i.e. the rules to add according to the Taclet goal template to the node
     * of the given goal)
     *
     * @param rules the rules to be added
     * @param goal the goal describing the node where the rules should be added
     * @param p_services the Services encapsulating all Rust information
     * @param p_matchCond the MatchConditions containing in particular the instantiations of the
     *        schemavariables
     */
    @Override
    protected void applyAddrule(ImmutableList<? extends org.key_project.prover.rules.Taclet> rules,
            @NonNull Goal goal, LogicServices p_services,
            org.key_project.prover.rules.MatchConditions p_matchCond) {
        var services = (Services) p_services;
        var matchCond = (MatchConditions) p_matchCond;
        for (var rule : rules) {
            var tacletToAdd = (Taclet) rule;
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
            for (var sv : collector.vars()) {
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



    @Override
    protected Term applyContextUpdate(org.key_project.prover.rules.inst.SVInstantiations p_svInst,
            Term formula, @NonNull Goal goal) {
        final var svInst = (SVInstantiations) p_svInst;
        if (svInst.getUpdateContext().isEmpty()) {
            return formula;
        } else {
            return goal.getOverlayServices().getTermBuilder()
                    .applyUpdatePairsSequential(svInst.getUpdateContext(), formula);
        }
    }

    protected void applyAddProgVars(ImmutableSet<org.key_project.logic.op.sv.SchemaVariable> pvs,
                                    SequentChangeInfo currentSequent,
                                    Goal goal,
                                    PosInOccurrence posOfFind,
                                    LogicServices p_services, org.key_project.prover.rules.MatchConditions matchCond) {
      // TODO
    }


        @Override
    protected SequentFormula createSequentFormula(Term form) {
        return new SequentFormula(form);
    }
}
