/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import java.util.ArrayList;
import java.util.Iterator;

import de.uka.ilkd.key.informationflow.po.BlockExecutionPO;
import de.uka.ilkd.key.informationflow.po.InfFlowContractPO;
import de.uka.ilkd.key.informationflow.po.LoopInvExecutionPO;
import de.uka.ilkd.key.informationflow.po.SymbolicExecutionPO;
import de.uka.ilkd.key.logic.op.SkolemTermSV;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.instantiation.AssumesFormulaInstantiation;
import org.key_project.prover.rules.instantiation.InstantiationEntry;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Semisequent;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableMapEntry;

import org.jspecify.annotations.NonNull;


public class InfFlowContractAppFeature implements Feature {

    public static final Feature INSTANCE = new InfFlowContractAppFeature();


    protected InfFlowContractAppFeature() {
    }


    /**
     * Compare whether two <code>PosInOccurrence</code>s are equal. This can be done using
     * <code>equals</code> or <code>eqEquals</code> (checking for same or equal formulas), which has
     * to be decided by the subclasses
     */
    protected final boolean comparePio(PosInOccurrence newPio, PosInOccurrence oldPio) {
        return oldPio.eqEquals(newPio);
    }


    /**
     * Check whether a semisequent contains a formula. Again, one can either search for the same or
     * an equal formula
     */
    protected boolean semiSequentContains(Semisequent semisequent, SequentFormula cfma) {
        return semisequent.containsEqual(cfma);
    }


    /**
     * Check whether the old rule application <code>ruleCmp</code> is a duplicate of the new
     * application <code>newApp</code> at position <code>newPio</code>.<code>newPio</code> can be
     * <code>null</code>
     */
    protected boolean sameApplication(RuleApp ruleCmp,
            TacletApp newApp, PosInOccurrence newPio) {
        // compare the rules
        if (newApp.rule() != ruleCmp.rule()) {
            return false;
        }

        final TacletApp cmp = (TacletApp) ruleCmp;

        // compare the position of application
        if (newPio != null) {
            if (!(cmp instanceof PosTacletApp)) {
                return false;
            }
            final PosInOccurrence oldPio = cmp.posInOccurrence();
            if (!comparePio(newPio, oldPio)) {
                return false;
            }
        }


        // compare the if-sequent instantiations
        if (newApp.assumesFormulaInstantiations() == null
                || cmp.assumesFormulaInstantiations() == null) {
            if (newApp.assumesFormulaInstantiations() != null
                    || cmp.assumesFormulaInstantiations() != null) {
                return false;
            }
        } else {
            final Iterator<AssumesFormulaInstantiation> it0 =
                newApp.assumesFormulaInstantiations().iterator();
            final Iterator<AssumesFormulaInstantiation> it1 =
                cmp.assumesFormulaInstantiations().iterator();

            while (it0.hasNext()) {
                // this test should be improved
                if (it0.next().getSequentFormula() != it1.next().getSequentFormula()) {
                    return false;
                }
            }
        }

        return equalInterestingInsts(newApp.instantiations(), cmp.instantiations());
    }


    private boolean equalInterestingInsts(SVInstantiations inst0, SVInstantiations inst1) {
        if (!inst0.getUpdateContext().equals(inst1.getUpdateContext())) {
            return false;
        }

        final var interesting0 = inst0.interesting();
        final var interesting1 = inst1.interesting();
        return subset(interesting0, interesting1) && subset(interesting1, interesting0);
    }


    private boolean subset(
            ImmutableMap<@NonNull SchemaVariable, InstantiationEntry<?>> insts0,
            ImmutableMap<@NonNull SchemaVariable, InstantiationEntry<?>> insts1) {

        for (final ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>> entry0 : insts0) {
            if (entry0.key() instanceof SkolemTermSV || entry0.key() instanceof VariableSV) {
                continue;
            }

            final InstantiationEntry<?> instEntry1 = insts1.get(entry0.key());

            if (instEntry1 == null
                    || !entry0.value().getInstantiation().equals(instEntry1.getInstantiation())) {
                return false;
            }
        }

        return true;
    }


    /**
     * Search for a duplicate of the application <code>app</code> by walking upwards in the proof
     * tree. Here, we assume that <code>pos</code> is non-null, and as an optimisation we stop as
     * soon as we have reached a point where the formula containing the focus no longer occurs in
     * the sequent
     */
    protected boolean duplicateFindTaclet(TacletApp app,
            PosInOccurrence pos, ProofGoal<?> goal) {
        assert pos != null : "Feature is only applicable to rules with find.";
        assert !app.assumesFormulaInstantiations().isEmpty()
                : "Featureis only applicable to rules with at least one assumes.";

        final SequentFormula focusFor = pos.sequentFormula();
        final boolean antec = pos.isInAntec();
        final SequentFormula assumesFor =
            app.assumesFormulaInstantiations().iterator().next().getSequentFormula();

        // assumtion has to occour before the find-term in the sequent in order
        // to avoid duplicated applications
        int focusPos = goal.sequent().formulaNumberInSequent(antec, focusFor);
        int assumesPos = goal.sequent().formulaNumberInSequent(antec, assumesFor);
        if (focusPos <= assumesPos) {
            return true;
        }

        Node node = ((Goal) goal).node();

        int i = 0;
        while (!node.root()) {
            final Node par = node.parent();

            ++i;
            if (i > 100) {
                i = 0;

                final Sequent pseq = par.sequent();
                if (antec) {
                    if (!semiSequentContains(pseq.antecedent(), focusFor)) {
                        return false;
                    }
                } else {
                    if (!semiSequentContains(pseq.succedent(), focusFor)) {
                        return false;
                    }
                }
            }

            if (sameApplication(par.getAppliedRuleApp(), app, pos)) {
                return true;
            }

            node = par;
        }

        return false;
    }


    @Override
    public <Goal extends ProofGoal<@NonNull Goal>> RuleAppCost computeCost(RuleApp ruleApp,
            PosInOccurrence pos, Goal goal, MutableState mState) {
        assert pos != null : "Feature is only applicable to rules with find.";
        assert ruleApp instanceof TacletApp : "Feature is only applicable " + "to Taclets.";
        TacletApp app = (TacletApp) ruleApp;

        if (!app.assumesInstantionsComplete()) {
            return NumberRuleAppCost.getZeroCost();
        }

        if (!isInfFlowProof((Proof) goal.proof()) || app.assumesFormulaInstantiations() == null
                || app.assumesFormulaInstantiations().isEmpty()
                || duplicateFindTaclet(app, pos, goal)) {
            return TopRuleAppCost.INSTANCE;
        }

        // only relate the n-th called method in execution A with the n-th
        // called method in execution B automatically
        final SequentFormula focusFor = pos.sequentFormula();
        final SequentFormula assumesFor =
            app.assumesFormulaInstantiations().iterator().next().getSequentFormula();

        ArrayList<SequentFormula> relatesTerms = getRelatesTerms(goal);
        final int numOfContractAppls = relatesTerms.size() / 2;
        int assumesApplNumber = 0;
        for (int i = 0; i < numOfContractAppls; i++) {
            if (relatesTerms.get(i).equals(assumesFor)) {
                assumesApplNumber = i;
                break;
            }
        }
        final int findApplNumber = assumesApplNumber + numOfContractAppls;
        if (!relatesTerms.get(findApplNumber).equals(focusFor)) {
            return TopRuleAppCost.INSTANCE;
        }

        return NumberRuleAppCost.create(assumesApplNumber);
    }


    private boolean isInfFlowProof(Proof proof) {
        ProofOblInput po = proof.getServices().getSpecificationRepository().getProofOblInput(proof);
        return po instanceof InfFlowContractPO || po instanceof SymbolicExecutionPO
                || po instanceof BlockExecutionPO || po instanceof LoopInvExecutionPO;
    }


    private ArrayList<SequentFormula> getRelatesTerms(ProofGoal<?> goal) {
        ArrayList<SequentFormula> list = new ArrayList<>();
        Semisequent antecedent = goal.sequent().antecedent();
        for (SequentFormula f : antecedent) {
            if (f.formula().op().toString().startsWith("RELATED_BY_")) {
                list.add(f);
            }
        }
        return list;
    }
}
