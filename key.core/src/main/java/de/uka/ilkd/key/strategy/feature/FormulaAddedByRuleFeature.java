/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.rulefilter.RuleFilter;
import de.uka.ilkd.key.rule.RuleApp;


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

    public boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
        assert pos != null : "Feature is only applicable to rules with find";

        final SequentFormula cfma = pos.sequentFormula();
        final boolean antec = pos.isInAntec();

        Node node = goal.node();

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
