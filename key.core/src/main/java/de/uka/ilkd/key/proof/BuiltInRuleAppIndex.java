/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.util.concurrent.atomic.AtomicLong;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

public class BuiltInRuleAppIndex {
    public static final AtomicLong PERF_CREATE_ALL = new AtomicLong();
    public static final AtomicLong PERF_UPDATE = new AtomicLong();
    private final BuiltInRuleIndex index;

    private SequentChangeInfo sequentChangeInfo = null;

    public BuiltInRuleAppIndex(BuiltInRuleIndex index) {
        this.index = index;
    }

    private BuiltInRuleAppIndex(BuiltInRuleIndex index, SequentChangeInfo sequentChangeInfo) {
        this.index = index;
        this.sequentChangeInfo = sequentChangeInfo;
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
        return new BuiltInRuleAppIndex(index.copy(),
            sequentChangeInfo == null ? null : sequentChangeInfo.copy());
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

    private static void scanSimplificationRule(ImmutableList<BuiltInRule> rules, Goal goal,
            boolean antec,
            NewRuleListener listener) {
        final Node node = goal.node();
        final Sequent seq = node.sequent();

        for (final SequentFormula sf : (antec ? seq.antecedent() : seq.succedent())) {
            scanSimplificationRule(rules, goal, antec, sf, listener);
        }
    }

    private static void scanSimplificationRule(ImmutableList<BuiltInRule> rules, Goal goal,
            boolean antec,
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
    private static void scanSimplificationRule(ImmutableList<BuiltInRule> rules, Goal goal,
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

    public void reportRuleApps(Goal goal, NewRuleListener l) {
        var time = System.nanoTime();
        scanSimplificationRule(goal, l);
        sequentChangeInfo = null;
        PERF_CREATE_ALL.getAndAdd(System.nanoTime() - time);
    }

    /**
     * called if a formula has been replaced
     *
     * @param sci SequentChangeInfo describing the change of the sequent
     */
    public void sequentChanged(SequentChangeInfo sci) {
        if (sequentChangeInfo == null) {
            // Nothing stored, store change
            sequentChangeInfo = sci.copy();
        } else {
            assert sequentChangeInfo.sequent() == sci.getOriginalSequent();
            sequentChangeInfo.combine(sci);
        }
    }

    public void resetSequentChanges() {
        sequentChangeInfo = null;
    }

    public void flushSequentChanges(Goal goal, NewRuleListener listener) {
        if (sequentChangeInfo == null) {
            return;
        }
        var time = System.nanoTime();
        scanAddedFormulas(goal, true, sequentChangeInfo, listener);
        scanAddedFormulas(goal, false, sequentChangeInfo, listener);

        scanModifiedFormulas(goal, true, sequentChangeInfo, listener);
        scanModifiedFormulas(goal, false, sequentChangeInfo, listener);
        sequentChangeInfo = null;
        PERF_UPDATE.getAndAdd(System.nanoTime() - time);
    }

    private void scanAddedFormulas(Goal goal, boolean antec, SequentChangeInfo sci,
            NewRuleListener listener) {
        ImmutableList<SequentFormula> cfmas = sci.addedFormulas(antec);
        while (!cfmas.isEmpty()) {
            final SequentFormula cfma = cfmas.head();
            scanSimplificationRule(index.rules(), goal, antec, cfma, listener);
            cfmas = cfmas.tail();
        }
    }


    private void scanModifiedFormulas(Goal goal, boolean antec, SequentChangeInfo sci,
            NewRuleListener listener) {
        ImmutableList<FormulaChangeInfo> fcis = sci.modifiedFormulas(antec);

        while (!fcis.isEmpty()) {
            final FormulaChangeInfo fci = fcis.head();
            final SequentFormula cfma = fci.getNewFormula();
            scanSimplificationRule(index.rules(), goal, antec, cfma, listener);
            fcis = fcis.tail();
        }
    }
}
