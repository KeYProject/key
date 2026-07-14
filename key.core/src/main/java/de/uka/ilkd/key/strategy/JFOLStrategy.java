/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.feature.RuleSetDispatchFeature;
import de.uka.ilkd.key.strategy.quantifierHeuristics.ClausesSmallerThanFeature;
import de.uka.ilkd.key.strategy.termProjection.FocusProjection;

import org.key_project.logic.Name;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.feature.SumFeature;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

/// This strategy extends the classical [FOLStrategy] with heuristics
/// for quantifier instantiation based on E-matching, which involves
/// normalization of quantified formulas, as well as term features depending on
/// integer theory.
///
/// Do not create directly; use [JFOLStrategyFactory] instead.
public class JFOLStrategy extends FOLStrategy {
    public static final Name NAME = new Name("JFOL Strategy");

    public JFOLStrategy(Proof proof, StrategyProperties strategyProperties) {
        super(proof, strategyProperties);
    }

    @Override
    protected void setupFormulaNormalisation(RuleSetDispatchFeature d) {
        super.setupFormulaNormalisation(d);
        var numbers = getServices().getTypeConverter().getIntegerLDT();
        bindRuleSet(d, "cnf_orComm",
            SumFeature.createSum(applyTF("commRight", ff.clause),
                applyTFNonStrict("commResidue", ff.clauseSet),
                or(applyTF("commLeft", ff.andF),
                    add(applyTF("commLeft", ff.literal),
                        literalsSmallerThan("commRight", "commLeft", numbers))),
                longConst(-100)));
        bindRuleSet(d, "cnf_andComm",
            SumFeature.createSum(applyTF("commLeft", ff.clause),
                applyTF("commRight", ff.clauseSet), applyTFNonStrict("commResidue", ff.clauseSet),
                // at least one of the subformulas has to be a literal;
                // otherwise, sorting is not likely to have any big effect
                ifZero(
                    add(applyTF("commLeft", not(ff.literal)),
                        applyTF("commRight", rec(ff.andF, not(ff.literal)))),
                    longConst(100), longConst(-60)),
                clausesSmallerThan("commRight", "commLeft", numbers)));
    }

    @Override
    protected void setupSplitting(RuleSetDispatchFeature d) {
        super.setupSplitting(d);
        var heapLDT = getServices().getTypeConverter().getHeapLDT();
        var vf = new ValueTermFeature(op(heapLDT.getNull()));
        ProjectionToTerm<Goal> cutFormula = instOf("cutFormula");
        bindRuleSet(d, "cut_direct",
            SumFeature
                    .createSum(
                        ifZero(notBelowQuantifier(),
                            add(
                                // prefer cuts over "something = null"
                                ifZero(applyTF(FocusProjection.INSTANCE,
                                    opSub(tf.eq, any(), vf.nullTerm)),
                                    longConst(-5), longConst(0)),
                                // punish cuts over formulas containing anon heap functions
                                ifZero(applyTF(cutFormula, rec(any(), not(anonHeapTermFeature()))),
                                    longConst(0), longConst(1000))))));
    }

    private Feature clausesSmallerThan(String smaller, String bigger, IntegerLDT numbers) {
        return ClausesSmallerThanFeature.create(instOf(smaller), instOf(bigger), numbers);
    }

    @Override
    public Name name() {
        return NAME;
    }
}
