/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;

import org.key_project.logic.PosInTerm;
import org.key_project.prover.sequent.*;
import org.key_project.prover.strategy.NewRuleListener;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

public class BuiltInRuleAppIndex {

    private final BuiltInRuleIndex index;

    private NewRuleListener newRuleListener = NullNewRuleListener.INSTANCE;

    public BuiltInRuleAppIndex(BuiltInRuleIndex index) {
        this.index = index;
    }


    public BuiltInRuleAppIndex(BuiltInRuleIndex index, NewRuleListener p_newRuleListener) {
        this.index = index;
        this.newRuleListener = p_newRuleListener;
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

    public void setNewRuleListener(NewRuleListener p_newRuleListener) {
        newRuleListener = p_newRuleListener;
    }

    public BuiltInRuleIndex builtInRuleIndex() {
        return index;
    }

    public void scanApplicableRules(Goal goal, NewRuleListener newRuleListener) {
        scanSimplificationRule(goal, newRuleListener);
    }

    private void scanSimplificationRule(Goal goal, NewRuleListener listener) {
        ImmutableList<BuiltInRule> rules = index.rules();
        if (!rules.isEmpty()) {
            do {
                final BuiltInRule builtInRule = rules.head();
                rules = rules.tail();
                if (builtInRule.isApplicable(goal, null)) {
                    IBuiltInRuleApp app = builtInRule.createApp(null, goal.proof().getServices());
                    listener.ruleAdded(app, null);
                }
            } while (!rules.isEmpty());
            scanSimplificationRule(index.rules(), goal, false, listener);
            scanSimplificationRule(index.rules(), goal, true, listener);
        }
    }

    private void scanSimplificationRule(ImmutableList<BuiltInRule> rules, Goal goal, boolean antec,
            NewRuleListener listener) {
        final Node node = goal.node();
        final Sequent seq = node.sequent();

        for (final SequentFormula sf : (antec ? seq.antecedent()
                : seq.succedent())) {
            scanSimplificationRule(rules, goal, antec, sf, listener);
        }
    }

    private void scanSimplificationRule(ImmutableList<BuiltInRule> rules, Goal goal, boolean antec,
            SequentFormula cfma, NewRuleListener listener) {
        final PosInOccurrence pos = new PosInOccurrence(cfma, PosInTerm.getTopLevel(), antec);
        ImmutableList<BuiltInRule> subrules = ImmutableSLList.nil();
        while (!rules.isEmpty()) {
            final BuiltInRule rule = rules.head();
            rules = rules.tail();
            if (rule.isApplicableOnSubTerms()) {
                subrules = subrules.prepend(rule);
            } else if (rule.isApplicable(goal, pos)) {
                final IBuiltInRuleApp app = rule.createApp(pos, goal.proof().getServices());
                listener.ruleAdded(app, pos);
            }
        }
        scanSimplificationRule(subrules, goal, pos, listener);
    }

    // TODO: optimise?
    private void scanSimplificationRule(ImmutableList<BuiltInRule> rules, Goal goal,
            PosInOccurrence pos, NewRuleListener listener) {
        ImmutableList<BuiltInRule> it = rules;
        while (!it.isEmpty()) {
            final BuiltInRule rule = it.head();
            it = it.tail();
            if (rule.isApplicable(goal, pos)) {
                IBuiltInRuleApp app = rule.createApp(pos, goal.proof().getServices());
                listener.ruleAdded(app, pos);
            }
        }
        for (int i = 0, n = pos.subTerm().arity(); i < n; i++) {
            scanSimplificationRule(rules, goal, pos.down(i), listener);
        }
    }

    public void reportRuleApps(NewRuleListener l, Goal goal) {
        scanSimplificationRule(goal, l);
    }

    /**
     * called if a formula has been replaced
     *
     * @param sci SequentChangeInfo describing the change of the sequent
     */
    public void sequentChanged(Goal goal,
            SequentChangeInfo sci,
            NewRuleListener listener) {
        scanAddedFormulas(goal, true, sci, listener);
        scanAddedFormulas(goal, false, sci, listener);

        scanModifiedFormulas(goal, true, sci, listener);
        scanModifiedFormulas(goal, false, sci, listener);
    }

    private void scanAddedFormulas(Goal goal, boolean antec,
            SequentChangeInfo sci,
            NewRuleListener listener) {
        ImmutableList<SequentFormula> cfmas =
            sci.addedFormulas(antec);
        while (!cfmas.isEmpty()) {
            final SequentFormula cfma = cfmas.head();
            scanSimplificationRule(index.rules(), goal, antec, cfma, listener);
            cfmas = cfmas.tail();
        }
    }


    private void scanModifiedFormulas(Goal goal, boolean antec,
            SequentChangeInfo sci,
            NewRuleListener listener) {
        ImmutableList<FormulaChangeInfo> fcis =
            sci.modifiedFormulas(antec);

        while (!fcis.isEmpty()) {
            final FormulaChangeInfo fci =
                fcis.head();
            final SequentFormula cfma = fci.newFormula();
            scanSimplificationRule(index.rules(), goal, antec, cfma, listener);
            fcis = fcis.tail();
        }
    }
}
