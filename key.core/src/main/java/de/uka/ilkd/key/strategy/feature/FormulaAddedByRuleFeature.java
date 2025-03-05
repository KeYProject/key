/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.proof.Node;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.proof.rulefilter.RuleFilter;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.feature.BinaryFeature;
import org.key_project.prover.strategy.costbased.feature.Feature;

import org.jspecify.annotations.NonNull;


/**
 * Binary feature that returns zero iff the find-formula of the concerned rule app was introduced by
 * a certain kind rule of rule (described via a <code>RuleFilter</code>)
 */
public class FormulaAddedByRuleFeature extends BinaryFeature {

    private final RuleFilter filter;

    private FormulaAddedByRuleFeature(RuleFilter p_filter) {
        filter = p_filter;
    }

    public static Feature create(RuleFilter p_filter) {
        return new FormulaAddedByRuleFeature(p_filter);
    }

    @Override
    public <Goal extends ProofGoal<@NonNull Goal>> boolean filter(RuleApp app, PosInOccurrence pos,
            Goal goal, MutableState mState) {
        assert pos != null : "Feature is only applicable to rules with find";

        final SequentFormula cfma = pos.sequentFormula();
        final boolean antec = pos.isInAntec();

        Node node = ((de.uka.ilkd.key.proof.Goal) goal).node();

        while (!node.root()) {
            final Node par = node.parent();
            final Sequent pseq = par.sequent();

            if (!(antec ? pseq.antecedent() : pseq.succedent()).contains(cfma)) {
                return filter.filter(par.getAppliedRuleApp().rule());
            }

            node = par;
        }

        return false;
    }

}
