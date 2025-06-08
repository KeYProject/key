/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.executor.javadl;

import java.util.Collection;
import java.util.HashMap;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.RenamingTable;
import de.uka.ilkd.key.logic.VariableNamer;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.ProgVarReplacer;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint;
import de.uka.ilkd.key.rule.inst.GenericSortCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Term;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.sequent.*;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NonNull;

/**
 * Encapsulates the application engine of taclets.
 *
 * Several methods require instantiationInformation objects:
 * in this implementation the following additional instantiation information concerning labels must
 * be provided:
 * <ul>
 * <li>termLabelState: The {@link TermLabelState} of the current rule application.</li>
 * <li>labelHint: The hint used to maintain {@link TermLabel}s. the instantiations of the
 * schemavariables</li>
 * </ul>
 *
 */
public abstract class TacletExecutor
        extends org.key_project.prover.rules.TacletExecutor<@NonNull Goal, @NonNull TacletApp> {

    protected TacletExecutor(Taclet taclet) {
        super(taclet);
    }

    @Override
    protected Term not(Term t, Goal goal) {
        return goal.getOverlayServices().getTermBuilder().not((JTerm) t);
    }

    @Override
    protected Term and(Term t1, Term t2, Goal goal) {
        return goal.getOverlayServices().getTermBuilder().and((JTerm) t1,
            (JTerm) t2);
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
     * @param tacletApp the {@link TacletApp} with application information
     * @param services the Services
     * @param instantiationInfo additional instantiation information concerning label:
     *        <ul>
     *        <li>termLabelState: The {@link TermLabelState} of the current rule application.</li>
     *        <li>labelHint: The hint used to maintain {@link TermLabel}s. the instantiations of the
     *        schemavariables</li>
     *        </ul>
     * @return the (partially) instantiated term
     */
    @Override
    protected Term syntacticalReplace(Term term,
            PosInOccurrence applicationPosInOccurrence,
            org.key_project.prover.rules.instantiation.MatchConditions mc,
            @NonNull Goal goal,
            @NonNull TacletApp tacletApp,
            LogicServices services,
            Object... /* TermLabelState, TacletLabelHint */ instantiationInfo) {
        final SyntacticalReplaceVisitor srVisitor =
            new SyntacticalReplaceVisitor((TermLabelState) instantiationInfo[0],
                (TacletLabelHint) instantiationInfo[1], applicationPosInOccurrence,
                (SVInstantiations) mc.getInstantiations(), goal,
                taclet, tacletApp);
        term.execPostOrder(srVisitor);
        return srVisitor.getTerm();
    }

    protected Term applyContextUpdate(
            org.key_project.prover.rules.instantiation.SVInstantiations p_svInst,
            Term formula, Goal goal) {
        // var instantiatedFormula = (de.uka.ilkd.key.logic.Term) formula;
        final SVInstantiations svInst = (SVInstantiations) p_svInst;
        if (svInst.getUpdateContext().isEmpty()) {
            return formula;
        }
        return goal.getOverlayServices().getTermBuilder()
                .applyUpdatePairsSequential(svInst.getUpdateContext(),
                    (JTerm) formula);
    }

    /**
     * instantiates the given semisequent with the instantiations found in Matchconditions
     *
     * @param semi the Semisequent to be instantiated
     * @param applicationPosInOccurrence The {@link PosInOccurrence} of the {@link Term} which is
     *        rewritten
     * @param matchCond the MatchConditions including the mapping Schemavariables to concrete logic
     *        elements
     * @param instantiationInfo additional instantiation information concerning label:
     *        <ul>
     *        <li>termLabelState: The {@link TermLabelState} of the current rule application.</li>
     *        <li>labelHint: The hint used to maintain {@link TermLabel}s. the instantiations of the
     *        schemavariables</li>
     *        </ul>
     * @return the instantiated formulas of the semisequent as list
     */
    @Override
    protected ImmutableList<SequentFormula> instantiateSemisequent(
            Semisequent semi,
            PosInOccurrence applicationPosInOccurrence,
            org.key_project.prover.rules.instantiation.MatchConditions matchCond, Goal goal,
            TacletApp tacletApp, LogicServices services,
            Object... instantiationInfo) { // TermLabelState termLabelState, TacletLabelHint
                                           // labelHint) {

        ImmutableList<SequentFormula> replacements = ImmutableSLList.nil();

        for (SequentFormula sf : semi) {
            replacements = replacements.append(instantiateReplacement(sf, services,
                matchCond, applicationPosInOccurrence, goal, tacletApp, instantiationInfo[0],
                new TacletLabelHint((TacletLabelHint) instantiationInfo[1], sf)));
        }

        return replacements;
    }

    /**
     * adds the given rules (i.e. the rules to add according to the Taclet goal template to the node
     * of the given goal)
     *
     * @param rules the rules to be added
     * @param goal the goal describing the node where the rules should be added
     * @param services the Services encapsulating all java information
     * @param p_matchCond the MatchConditions containing in particular the instantiations of the
     *        schemavariables
     */
    @Override
    protected void applyAddrule(ImmutableList<? extends org.key_project.prover.rules.Taclet> rules,
            @NonNull Goal goal,
            LogicServices services,
            org.key_project.prover.rules.instantiation.MatchConditions p_matchCond) {
        var matchCond = (MatchConditions) p_matchCond;
        for (var tacletToAdd : rules) {
            final Node n = goal.node();
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

    @Override
    protected void applyAddProgVars(ImmutableSet<SchemaVariable> pvs,
            SequentChangeInfo currentSequent,
            Goal goal,
            PosInOccurrence posOfFind,
            LogicServices p_services,
            org.key_project.prover.rules.instantiation.MatchConditions matchCond) {
        final Services services = (Services) p_services;
        ImmutableList<RenamingTable> renamings = ImmutableSLList.nil();
        for (final SchemaVariable sv : pvs) {
            final LocationVariable inst =
                (LocationVariable) matchCond.getInstantiations().getInstantiation(sv);
            // if the goal already contains the variable to be added
            // (not just a variable with the same name), then there is nothing to do
            Collection<IProgramVariable> progVars =
                goal.getLocalNamespaces().programVariables().elements();
            if (progVars.contains(inst)) {
                continue;
            }

            final VariableNamer vn = services.getVariableNamer();
            final LocationVariable renamedInst = vn.rename(inst, goal, posOfFind);
            goal.addProgramVariable(renamedInst);
            services.addNameProposal(renamedInst.name());

            final HashMap<LocationVariable, LocationVariable> renamingMap = vn.getRenamingMap();
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
        goal.node().setRenamings(renamings);
    }


}
