/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof;

import org.key_project.logic.PosInTerm;
import org.key_project.prover.sequent.*;
import org.key_project.rusty.logic.*;
import org.key_project.rusty.rule.BuiltInRule;
import org.key_project.rusty.rule.IBuiltInRuleApp;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

public class BuiltInRuleAppIndex {
    private final BuiltInRuleIndex index;

    public BuiltInRuleAppIndex(BuiltInRuleIndex index) {
        this.index = index;
    }

    /**
     * returns a list of built-in rules application applicable for the given goal and position
     */
    public ImmutableList<IBuiltInRuleApp> getBuiltInRule(Goal goal, PosInOccurrence pos) {

        ImmutableList<IBuiltInRuleApp> result = ImmutableSLList.nil();

        ImmutableList<BuiltInRule> rules = index.rules();
        while (!rules.isEmpty()) {
            final BuiltInRule bir = rules.head();
            rules = rules.tail();
            if (bir.isApplicable(goal, pos)) {
                IBuiltInRuleApp app = bir.createApp(pos, goal.proof().getServices());
                result = result.prepend(app);
            }
        }
        return result;
    }


    /**
     * returns a copy of this index
     */
    public BuiltInRuleAppIndex copy() {
        return new BuiltInRuleAppIndex(index.copy());
    }

    public BuiltInRuleIndex builtInRuleIndex() {
        return index;
    }

    public void scanApplicableRules(Goal goal) {
        scanSimplificationRule(goal);
    }

    private void scanSimplificationRule(Goal goal) {
        ImmutableList<BuiltInRule> rules = index.rules();
        if (!rules.isEmpty()) {
            do {
                final BuiltInRule builtInRule = rules.head();
                rules = rules.tail();
                if (builtInRule.isApplicable(goal, null)) {
                    IBuiltInRuleApp app = builtInRule.createApp(null, goal.proof().getServices());
                    // listener.ruleAdded(app, null);
                }
            } while (!rules.isEmpty());
            scanSimplificationRule(index.rules(), goal, false);
            scanSimplificationRule(index.rules(), goal, true);
        }
    }

    private void scanSimplificationRule(ImmutableList<BuiltInRule> rules, Goal goal,
            boolean antec) {
        final Node node = goal.getNode();
        final Sequent seq = node.sequent();

        for (final SequentFormula sf : (antec ? seq.antecedent() : seq.succedent())) {
            scanSimplificationRule(rules, goal, antec, sf);
        }
    }

    private void scanSimplificationRule(ImmutableList<BuiltInRule> rules, Goal goal, boolean antec,
            SequentFormula cfma) {
        final PosInOccurrence pos = new PosInOccurrence(cfma, PosInTerm.getTopLevel(), antec);
        ImmutableList<BuiltInRule> subrules = ImmutableSLList.nil();
        while (!rules.isEmpty()) {
            final BuiltInRule rule = rules.head();
            rules = rules.tail();
            if (rule.isApplicableOnSubTerms()) {
                subrules = subrules.prepend(rule);
            } else if (rule.isApplicable(goal, pos)) {
                final IBuiltInRuleApp app = rule.createApp(pos, goal.proof().getServices());
                // listener.ruleAdded(app, pos);
            }
        }
        scanSimplificationRule(subrules, goal, pos);
    }

    // TODO: optimise?
    private void scanSimplificationRule(ImmutableList<BuiltInRule> rules, Goal goal,
            PosInOccurrence pos) {
        ImmutableList<BuiltInRule> it = rules;
        while (!it.isEmpty()) {
            final BuiltInRule rule = it.head();
            it = it.tail();
            if (rule.isApplicable(goal, pos)) {
                IBuiltInRuleApp app = rule.createApp(pos, goal.proof().getServices());
                // listener.ruleAdded(app, pos);
            }
        }
        for (int i = 0, n = pos.subTerm().arity(); i < n; i++) {
            scanSimplificationRule(rules, goal, pos.down(i));
        }
    }

    public void reportRuleApps(Goal goal) {
        scanSimplificationRule(goal);
    }

    /**
     * called if a formula has been replaced
     *
     * @param sci SequentChangeInfo describing the change of the sequent
     */
    public void sequentChanged(Goal goal, SequentChangeInfo sci) {
        scanAddedFormulas(goal, true, sci);
        scanAddedFormulas(goal, false, sci);

        scanModifiedFormulas(goal, true, sci);
        scanModifiedFormulas(goal, false, sci);
    }

    private void scanAddedFormulas(Goal goal, boolean antec, SequentChangeInfo sci) {
        ImmutableList<SequentFormula> cfmas = sci.addedFormulas(antec);
        while (!cfmas.isEmpty()) {
            final SequentFormula cfma = cfmas.head();
            scanSimplificationRule(index.rules(), goal, antec, cfma);
            cfmas = cfmas.tail();
        }
    }


    private void scanModifiedFormulas(Goal goal, boolean antec, SequentChangeInfo sci) {
        ImmutableList<FormulaChangeInfo> fcis = sci.modifiedFormulas(antec);

        while (!fcis.isEmpty()) {
            final FormulaChangeInfo fci = fcis.head();
            final SequentFormula cfma = fci.newFormula();
            scanSimplificationRule(index.rules(), goal, antec, cfma);
            fcis = fcis.tail();
        }
    }
}
