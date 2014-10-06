// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.collection.ImmutableMap;
import de.uka.ilkd.key.collection.ImmutableMapEntry;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SkolemTermSV;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.BlockExecutionPO;
import de.uka.ilkd.key.proof.init.InfFlowContractPO;
import de.uka.ilkd.key.proof.init.LoopInvExecutionPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.init.SymbolicExecutionPO;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.InstantiationEntry;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;
import java.util.ArrayList;
import java.util.Iterator;


public class InfFlowContractAppFeature implements Feature {

    public static final Feature INSTANCE = new InfFlowContractAppFeature();


    protected InfFlowContractAppFeature() {
    }


    /**
     * Compare whether two
     * <code>PosInOccurrence</code>s are equal. This can be done using
     * <code>equals</code> or
     * <code>eqEquals</code> (checking for same or equal formulas), which has to
     * be decided by the subclasses
     */
    protected boolean comparePio(TacletApp newApp,
                                 TacletApp oldApp,
                                 PosInOccurrence newPio,
                                 PosInOccurrence oldPio) {
        return oldPio.eqEquals(newPio);
    }


    /**
     * Check whether a semisequent contains a formula. Again, one can either
     * search for the same or an equal formula
     */
    protected boolean semiSequentContains(Semisequent semisequent,
                                          SequentFormula cfma) {
        return semisequent.containsEqual(cfma);
    }


    /**
     * Check whether the old rule application
     * <code>ruleCmp</code> is a duplicate of the new application
     * <code>newApp</code> at position
     * <code>newPio</code>.<code>newPio</code> can be
     * <code>null</code>
     */
    protected boolean sameApplication(RuleApp ruleCmp,
                                      TacletApp newApp,
                                      PosInOccurrence newPio) {
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
            final PosInOccurrence oldPio =
                    ((PosTacletApp) cmp).posInOccurrence();
            if (!comparePio(newApp, cmp, newPio, oldPio)) {
                return false;
            }
        }


        // compare the if-sequent instantiations
        if (newApp.ifFormulaInstantiations() == null ||
            cmp.ifFormulaInstantiations() == null) {
            if (newApp.ifFormulaInstantiations() != null ||
                cmp.ifFormulaInstantiations() != null) {
                return false;
            }
        } else {
            final Iterator<IfFormulaInstantiation> it0 =
                    newApp.ifFormulaInstantiations().iterator();
            final Iterator<IfFormulaInstantiation> it1 =
                    cmp.ifFormulaInstantiations().iterator();

            while (it0.hasNext()) {
                // this test should be improved
                if (it0.next().getConstrainedFormula() !=
                    it1.next().getConstrainedFormula()) {
                    return false;
                }
            }
        }

        return equalInterestingInsts(newApp.instantiations(),
                                     cmp.instantiations());
    }


    private boolean equalInterestingInsts(SVInstantiations inst0,
                                          SVInstantiations inst1) {
        if (!inst0.getUpdateContext().equals(inst1.getUpdateContext())) {
            return false;
        }

        final ImmutableMap<SchemaVariable, InstantiationEntry<?>> interesting0 =
                inst0.interesting();
        final ImmutableMap<SchemaVariable, InstantiationEntry<?>> interesting1 =
                inst1.interesting();
        return subset(interesting0, interesting1) &&
               subset(interesting1, interesting0);
    }


    private boolean subset(
            ImmutableMap<SchemaVariable, InstantiationEntry<?>> insts0,
            ImmutableMap<SchemaVariable, InstantiationEntry<?>> insts1) {
        final Iterator<ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>>> it =
                insts0.entryIterator();

        while (it.hasNext()) {
            final ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>> entry0 =
                    it.next();

            if (entry0.key() instanceof SkolemTermSV ||
                entry0.key() instanceof VariableSV) {
                continue;
            }

            final InstantiationEntry<?> instEntry1 = insts1.get(entry0.key());

            if (instEntry1 == null ||
                !entry0.value().getInstantiation().equals(instEntry1.getInstantiation())) {
                return false;
            }
        }

        return true;
    }


    /**
     * Search for a duplicate of the application
     * <code>app</code> by walking upwards in the proof tree. Here, we assume
     * that
     * <code>pos</code> is non-null, and as an optimisation we stop as soon as
     * we have reached a point where the formula containing the focus no longer
     * occurs in the sequent
     */
    protected boolean duplicateFindTaclet(TacletApp app,
                                          PosInOccurrence pos,
                                          Goal goal) {
        assert pos != null : "Feature is only applicable to rules with find.";
        assert app.ifFormulaInstantiations().size() >= 1 :
                "Featureis only applicable to rules with at least one assumes.";

        final SequentFormula focusFor = pos.constrainedFormula();
        final boolean antec = pos.isInAntec();
        final SequentFormula assumesFor =
                app.ifFormulaInstantiations().iterator().next().getConstrainedFormula();

        // assumtion has to occour before the find-term in the sequent in order
        // to avoid duplicated applications
        int focusPos =
                goal.node().sequent().formulaNumberInSequent(antec, focusFor);
        int assumesPos =
                goal.node().sequent().formulaNumberInSequent(antec, assumesFor);
        if (focusPos <= assumesPos) {
            return true;
        }

        Node node = goal.node();

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
    public RuleAppCost compute(RuleApp ruleApp,
                               PosInOccurrence pos,
                               Goal goal) {
        assert pos != null : "Feature is only applicable to rules with find.";
        assert ruleApp instanceof TacletApp : "Feature is only applicable " +
                                              "to Taclets.";
        TacletApp app = (TacletApp) ruleApp;

        if (!app.ifInstsComplete()) {
            return NumberRuleAppCost.getZeroCost();
        }
        
        if (app.ifFormulaInstantiations().size() < 1 ||
            !isInfFlowProof(goal.proof()) ||
            duplicateFindTaclet(app, pos, goal)) {
            return TopRuleAppCost.INSTANCE;
        }

        // only relate the n-th called method in execution A with the n-th
        // called method in execution B automatically
        final SequentFormula focusFor = pos.constrainedFormula();
        final SequentFormula assumesFor =
                app.ifFormulaInstantiations().iterator().next().getConstrainedFormula();

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
        ProofOblInput po =
                proof.getServices().getSpecificationRepository().getProofOblInput(proof);
        return po instanceof InfFlowContractPO ||
               po instanceof SymbolicExecutionPO ||
               po instanceof BlockExecutionPO ||
               po instanceof LoopInvExecutionPO;
    }


    private ArrayList<SequentFormula> getRelatesTerms(Goal goal) {
        ArrayList<SequentFormula> list = new ArrayList<SequentFormula>();
        Semisequent antecedent = goal.node().sequent().antecedent();
        for (SequentFormula f : antecedent) {
            if (f.formula().op().toString().startsWith("RELATED_BY_")) {
                list.add(f);
            }
        }
        return list;
    }
}
