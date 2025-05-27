/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import java.util.Collection;
import java.util.HashMap;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Term;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Semisequent;
import org.key_project.prover.sequent.SequentChangeInfo;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.pat.BindingPattern;
import org.key_project.rusty.logic.*;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.proof.Goal;
import org.key_project.rusty.proof.Node;
import org.key_project.rusty.proof.ProgVarReplacer;
import org.key_project.rusty.rule.inst.GenericSortCondition;
import org.key_project.rusty.rule.inst.SVInstantiations;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import org.checkerframework.checker.nullness.qual.NonNull;

public abstract class TacletExecutor extends
        org.key_project.prover.rules.TacletExecutor<@NonNull Goal, @NonNull RuleApp> {
    protected TacletExecutor(Taclet taclet) {
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
            org.key_project.prover.rules.instantiation.MatchConditions mc, @NonNull Goal goal,
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
            org.key_project.prover.rules.instantiation.MatchConditions p_matchCond) {
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

    protected void applyAddProgVars(ImmutableSet<org.key_project.logic.op.sv.SchemaVariable> pvs,
            SequentChangeInfo currentSequent, Goal goal, PosInOccurrence posOfFind,
            Services services, MatchConditions matchCond) {
        ImmutableList<RenamingTable> renamings = ImmutableSLList.nil();
        for (final SchemaVariable sv : pvs) {
            final var instObj = matchCond.getInstantiations().getInstantiation(sv);
            final var inst = instObj instanceof BindingPattern bp ? bp.pv()
                    : (ProgramVariable) instObj;
            // if the goal already contains the variable to be added
            // (not just a variable with the same name), then there is nothing to do
            Collection<ProgramVariable> progVars =
                goal.getLocalNamespaces().programVariables().elements();
            if (progVars.contains(inst)) {
                continue;
            }
            final VariableNamer vn = services.getVariableNamer();
            final ProgramVariable renamedInst = vn.rename(inst, goal, posOfFind);
            goal.addProgramVariable(renamedInst);
            services.addNameProposal(renamedInst.name());

            final HashMap<ProgramVariable, ProgramVariable> renamingMap = vn.getRenamingMap();
            if (!renamingMap.isEmpty()) {
                // execute renaming
                final ProgVarReplacer pvr = new ProgVarReplacer(renamingMap, services);

                // globals
                // we do not need to do the old assignment
                // goal.setGlobalProgVars(pvr.replace(Immutables.createSetFrom(progVars)));
                // as the following assertions ensure it would have no effect anyway.
                assert renamingMap.size() == 1;
                assert renamingMap.get(inst) == renamedInst;
                assert !progVars.contains(inst);

                // taclet apps
                pvr.replace(goal.ruleAppIndex().tacletIndex());

                // sequent
                currentSequent.combine(pvr.replace(currentSequent.sequent()));

                final RenamingTable rt = RenamingTable.getRenamingTable(vn.getRenamingMap());

                renamings = renamings.append(rt);
            }
        }
        goal.getNode().setRenamings(renamings);
    }

    /**
     * adds SequentFormula to antecedent depending on position information (if none is handed over
     * it is added at the head of the antecedent). Of course, it has to be ensured that the position
     * information describes one occurrence in the antecedent of the sequent.
     *
     * @param semi the Semisequent with the ConstrainedFormulae to be added
     * @param currentSequent the Sequent which is the current (intermediate) result of applying the
     *        taclet
     * @param pos the PosInOccurrence describing the place in the sequent or null for head of
     *        antecedent
     * @param applicationPosInOccurrence The {@link PosInOccurrence} of the {@link Term} which is
     *        rewritten
     * @param matchCond the MatchConditions containing in particular the instantiations of the
     *        schemavariables
     * @param services the Services encapsulating all Rust information
     */
    protected void addToAntec(Semisequent semi, SequentChangeInfo currentSequent,
            PosInOccurrence pos,
            PosInOccurrence applicationPosInOccurrence, MatchConditions matchCond, Goal goal,
            RuleApp tacletApp, Services services) {
        addToPos(semi, currentSequent, pos, applicationPosInOccurrence, true,
            matchCond, goal, tacletApp, services);
    }


    @Override
    protected Term applyContextUpdate(
            org.key_project.prover.rules.instantiation.SVInstantiations p_svInst,
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
            LogicServices p_services,
            org.key_project.prover.rules.instantiation.MatchConditions matchCond) {
        // TODO
    }


    @Override
    protected SequentFormula createSequentFormula(Term form) {
        return new SequentFormula(form);
    }
}
