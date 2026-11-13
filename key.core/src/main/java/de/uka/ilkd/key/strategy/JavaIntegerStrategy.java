/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.strategy;


import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.feature.*;
import de.uka.ilkd.key.strategy.termProjection.*;
import de.uka.ilkd.key.strategy.termgenerator.SuperTermGenerator;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.Term;
import org.key_project.logic.TermOrdering;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.strategy.ComponentStrategy;
import org.key_project.prover.strategy.IFormulaTermFeatures;
import org.key_project.prover.strategy.IntegerStrategy;
import org.key_project.prover.strategy.costbased.DivModCost;
import org.key_project.prover.strategy.costbased.feature.*;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;

import org.jspecify.annotations.NonNull;


/// This strategy implements reasoning for integer arithmetics. In particular,
/// it supports linear integer arithmetics via Gaussian elimination,
/// Fourier-Motzkin; and non-linear integer reasoning via cross-multiplication
/// and Gröbner basis.
///
/// Do not create directly, instead use [IntegerStrategyFactory].
public class JavaIntegerStrategy extends IntegerStrategy<Goal> implements ComponentStrategy<Goal> {
    private final Proof proof;

    /// Caps how often a cross multiplication is applied on a branch.
    /// Justified by empirical measurements. Candidate to be exposed in
    /// a settings strategy pane (not the strategy pane)
    private static final int BRANCH_MULT_CAP = 8;

    public JavaIntegerStrategy(Config cfg, IFormulaTermFeatures ff, Proof proof) {
        super(cfg, ff,
            new JavaFeatureConstants());
        this.proof = proof;
        init();
    }

    @Override
    protected void setupApprovalDispatcher(RuleSetDispatchFeature d) {
        super.setupApprovalDispatcher(d);

        bindRuleSet(d, "defOps_jdiv", NonDuplicateAppModPositionFeature.INSTANCE);
    }

    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////
    //
    // Axiomatisation and algorithms for further arithmetic operations:
    // division, modulus, modular Java operations
    //
    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////

    protected void setupDefOpsPrimaryCategories(RuleSetDispatchFeature d) {
        super.setupDefOpsPrimaryCategories(d);
        if (arith != ArithTreatment.BASIC) {
            bindRuleSet(d, "defOps_jdiv",
                SumFeature.createSum(NonDuplicateAppModPositionFeature.INSTANCE,
                    applyTF("divNum", tf.polynomial), applyTF("divDenom", tf.polynomial),
                    applyTF("divNum", tf.notContainsDivMod),
                    applyTF("divDenom", tf.notContainsDivMod),
                    ifZero(isBelow(ff.modalOperator()), longConst(DivModCost.BELOW_MODALITY))));

            bindRuleSet(d, "defOps_jdiv_inline", add(applyTF("divNum", tf.literal),
                applyTF("divDenom", tf.polynomial), longConst(DivModCost.INLINE)));
        } else {
            bindRuleSet(d, "defOps_jdiv", inftyConst());
            bindRuleSet(d, "defOps_jdiv_inline", add(applyTF("divNum", tf.literal),
                applyTF("divDenom", tf.literal), longConst(DivModCost.MOD)));
        }
    }

    @Override
    protected Feature getBranchCountFeatureFor(String prefix) {
        return BranchMultiplicationCountFeature.atMost(prefix, BRANCH_MULT_CAP);
    }

    @Override
    protected RuleSet getHeuristic(String p_name) {
        final NamespaceSet nss = proof.getNamespaces();
        final Namespace<@NonNull RuleSet> ns = nss.ruleSets();
        final RuleSet h = ns.lookup(new Name(p_name));

        assert h != null : "Did not find the rule set " + p_name;

        return h;
    }

    @Override
    protected Feature isBelow(TermFeature t) {
        final TermBuffer superTerm = new TermBuffer();
        return not(sum(superTerm, SuperTermGenerator.upwards(any(), proof.getServices()),
            not(applyTF(superTerm, t))));
    }

    @Override
    protected Term zTerm(String num) {
        return proof.getServices().getTermBuilder().zTerm(num);
    }

    @Override
    protected LogicServices getServices() {
        return proof.getServices();
    }

    @Override
    protected TermOrdering createTermOrdering() {
        return StaticFeatureCollection.createTermOrdering();
    }
}
