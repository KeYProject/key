/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.merge;

import java.util.ArrayList;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.MergePointStatement;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.AbstractBuiltInRuleApp;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.merge.MergeRule.MergeRuleProgressListener;
import de.uka.ilkd.key.rule.merge.procedures.MergeWithLatticeAbstraction;
import de.uka.ilkd.key.speclang.MergeContract;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;
import de.uka.ilkd.key.util.mergerule.SymbolicExecutionState;
import de.uka.ilkd.key.util.mergerule.SymbolicExecutionStateWithProgCnt;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Rule application class for merge rule applications. Is complete iff the mergePartners field as
 * well as the concrete {@link MergeProcedure} to be used have been set by the corresponding setter
 * function.
 *
 * @author Dominic Scheurer
 */
@NullMarked
public class MergeRuleBuiltInRuleApp extends AbstractBuiltInRuleApp<MergeRule> {

    // TODO: Make fields final and remove setters (create new app instead)
    private @Nullable Node mergeNode = null;
    private @Nullable ImmutableList<MergePartner> mergePartners = null;
    private @Nullable MergeProcedure concreteRule = null;

    private @Nullable SymbolicExecutionStateWithProgCnt thisSEState = null;
    private @Nullable ImmutableList<SymbolicExecutionState> mergePartnerStates = null;
    private @Nullable JTerm distForm = null;

    private final ArrayList<MergeRule.MergeRuleProgressListener> progressListeners =
        new ArrayList<>();

    public MergeRuleBuiltInRuleApp(MergeRule builtInRule, PosInOccurrence pio) {
        super(builtInRule, pio);
    }

    protected MergeRuleBuiltInRuleApp(MergeRule rule, PosInOccurrence pio,
            ImmutableList<PosInOccurrence> ifInsts) {
        super(rule, pio, ifInsts);
    }

    public MergeRuleBuiltInRuleApp(MergeRule rule, PosInOccurrence pio,
            ImmutableList<PosInOccurrence> ifInsts, Node mergeNode,
            ImmutableList<MergePartner> mergePartners, MergeProcedure concreteRule,
            SymbolicExecutionStateWithProgCnt thisSEState,
            ImmutableList<SymbolicExecutionState> mergePartnerStates, JTerm distForm,
            ArrayList<MergeRuleProgressListener> progressListeners) {
        super(rule, pio, ifInsts);
        this.mergeNode = mergeNode;
        this.mergePartners = mergePartners;
        this.concreteRule = concreteRule;
        this.thisSEState = thisSEState;
        this.mergePartnerStates = mergePartnerStates;
        this.distForm = distForm;
        this.progressListeners.addAll(progressListeners);
    }

    @Override
    public @Nullable MergeRuleBuiltInRuleApp replacePos(PosInOccurrence newPos) {
        return null;
    }

    @Override
    public IBuiltInRuleApp setAssumesInsts(ImmutableList<PosInOccurrence> ifInsts) {
        setMutable(ifInsts);
        return this;
    }

    @Override
    public MergeRuleBuiltInRuleApp tryToInstantiate(Goal goal) {
        // We assume that this method is *only* called for situations where the
        // current active statement is a MergePointStatement. Manual state
        // merging is still possible, but then this method shouldn't be called
        // (completion task is done by the corresponding visual dialogs).

        final ImmutableList<MergePartner> mergePartners =
            MergeRule.findPotentialMergePartners(goal, pio);

        if (mergePartners.isEmpty()) {
            return this;
        }

        final MergePointStatement mps = (MergePointStatement) JavaTools
                .getActiveStatement(TermBuilder.goBelowUpdates((JTerm) pio.subTerm()).javaBlock());

        final Services services = goal.proof().getServices();
        final MergeContract mc =
            services.getSpecificationRepository().getMergeContracts(mps).iterator().next();

        final Node node = goal.node();

        return new MergeRuleBuiltInRuleApp(super.builtInRule, super.pio, super.ifInsts, node,
            mergePartners, mc.getInstantiatedMergeProcedure(services),
            MergeRuleUtils.sequentToSETriple(node, pio, services),
            MergeRuleUtils.sequentsToSEPairs(mergePartners), null, new ArrayList<>());
    }

    @Override
    public boolean complete() {
        // We do not check for the suitability of the distinguishing formula
        // since this has already been dealt with in MergeRuleCompletion.
        return mergePartners != null && !mergePartners.isEmpty() && concreteRule != null
                && mergeNode != null && distinguishablePathConditionsRequirement();
    }

    private boolean distinguishablePathConditionsRequirement() {
        final Services services = mergeNode.proof().getServices();

        // NOTE: Requiring distinguishable path conditions for the abstraction
        // procedures here is an intermediate construction: MergeRule returns
        // if-then-else terms along with abstraction values when lattice
        // abstraction is applied; furthermore, if-then-else is a fallback
        // for unsupported data types.
        // Future finalization: Remove if-then-else fallbacks (can however
        // affect completeness) and check for each variable in the symbolic
        // states whether the corresponding data types are supported by
        // the concrete lattice.
        if (concreteRule.requiresDistinguishablePathConditions()
                || concreteRule instanceof MergeWithLatticeAbstraction) {
            ImmutableList<SymbolicExecutionState> allStates = ImmutableSLList.nil();
            allStates = allStates.prepend(mergePartnerStates);
            allStates = allStates.prepend(thisSEState.toSymbolicExecutionState());

            for (SymbolicExecutionState state1 : allStates) {
                for (SymbolicExecutionState state2 : allStates) {
                    if (state1 != state2) {
                        if (!MergeRuleUtils.pathConditionsAreDistinguishable(state1.second,
                            state2.second, services)) {
                            return false;
                        }
                    }
                }
            }

            return true;
        } else {
            return true;
        }
    }

    // GETTERS AND SETTERS //

    public ImmutableList<MergePartner> getMergePartners() {
        return mergePartners;
    }

    public void setMergePartners(ImmutableList<MergePartner> mergePartners) {
        this.mergePartners = mergePartners;
        mergePartnerStates = MergeRuleUtils.sequentsToSEPairs(mergePartners);
    }

    public MergeProcedure getConcreteRule() {
        return concreteRule;
    }

    public void setConcreteRule(MergeProcedure concreteRule) {
        this.concreteRule = concreteRule;
    }

    public Node getMergeNode() {
        return mergeNode;
    }

    public void setMergeNode(Node mergeNode) {
        this.mergeNode = mergeNode;
        this.thisSEState =
            MergeRuleUtils.sequentToSETriple(mergeNode, super.pio, mergeNode.proof().getServices());
    }

    public void setDistinguishingFormula(JTerm distForm) {
        // null is OK: In this case, we generate the distinguishing
        // formula automatically. Otherwise, the term must indeed be
        // a formula.
        assert distForm == null || distForm.sort() == JavaDLTheory.FORMULA;

        this.distForm = distForm;
    }

    public JTerm getDistinguishingFormula() {
        return distForm;
    }

    public SymbolicExecutionStateWithProgCnt getMergeSEState() {
        return thisSEState;
    }

    public ImmutableList<SymbolicExecutionState> getMergePartnerStates() {
        return mergePartnerStates;
    }

    public void registerProgressListener(MergeRule.MergeRuleProgressListener listener) {
        progressListeners.add(listener);
    }

    public void clearProgressListeners() {
        progressListeners.clear();
    }

    public boolean removeProgressListener(MergeRule.MergeRuleProgressListener listener) {
        return progressListeners.remove(listener);
    }

    public void fireProgressChange(int progress) {
        progressListeners.forEach(l -> l.signalProgress(progress));
    }

}
