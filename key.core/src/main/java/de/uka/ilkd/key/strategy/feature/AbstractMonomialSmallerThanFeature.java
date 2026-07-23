/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import java.util.Map;

import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.op.SkolemTermSV;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.RuleSet;
import org.key_project.util.collection.ImmutableList;

public abstract class AbstractMonomialSmallerThanFeature extends SmallerThanFeature {

    private static final Name newSymRuleSetName = new Name("polySimp_newSmallSym");
    private final Function add, mul, Z;


    protected AbstractMonomialSmallerThanFeature(IntegerLDT numbers) {
        this.add = numbers.getAdd();
        this.mul = numbers.getMul();
        this.Z = numbers.getNumberSymbol();
    }

    /**
     * if {@code op} is a Skolem constant the returned introduction time is the number of taclets
     * applied before and including the taclet by which it was introduced. <strong>For all other
     * operators the returned value is -1</strong>
     *
     * <p>
     * Although this reads the goal, the value is a constant for every operator a cost evaluation
     * can encounter, which is what makes features built on it {@code StableCost}-classifiable:
     * <ol>
     * <li>The compared terms are instantiation terms of the taclet app, so an operator seen here
     * either occurs in the goal's sequent or is the app's own fresh {@code SkolemTermSV}
     * instantiation.</li>
     * <li>A sequent operator with a {@code polySimp_newSmallSym} introducer: that application is
     * already part of the goal's applied-rule sequence (a symbol cannot occur before the
     * application that created it), and its position there never changes; every goal in which the
     * symbol occurs lies below the introduction and so agrees on that position. The value is the
     * same at every evaluation.</li>
     * <li>A sequent operator without such an introducer answers {@code -1}, and stays {@code -1}:
     * skolem instantiations are always fresh symbols ({@code TacletApp.createSkolemConstant}), so
     * no later application can become the introducer of an already existing operator.</li>
     * <li>An app's own fresh skolem symbol answers {@code -1} for as long as the app exists: its
     * introducer would be the app itself, which is unapplied while the app is pending, and once
     * applied the app is consumed, so no further evaluation of it takes place.</li>
     * </ol>
     * Case 4 is also the reason the {@code -1} answer must not be cached below: for that symbol
     * the answer changes the moment the introducing taclet is applied, and a frozen {@code -1}
     * would then leak into evaluations of other apps.
     * </p>
     *
     * @param op the Operator whose introduction time is queried
     * @param goal the Goal whose state is queried
     * @return the introduction time or -1 if not yet introduced or op is not a Skolem constant
     */
    protected int introductionTime(Operator op, Goal goal) {
        if (op == add || op == mul || op == Z) {
            return -1;
        }

        // A taclet with rule set "polySimp_newSmallSym" introduces its symbol as a SkolemTermSV
        // instantiation, which is always a skolem-constant function
        // (TacletApp.createSkolemConstant).
        // So an op that is not a skolem-constant function can never have been introduced by one:
        // its time is -1, with no need to scan the applied-rule history. This is what made the
        // scan a hotspot -- the common monomial atoms (program variables, ordinary functions) are
        // not skolem constants, yet walked the full O(history) on every compare and, never being
        // "introduced", were never cached. (A skolem constant from some OTHER rule still walks and
        // returns -1; only the structurally-impossible ops are short-circuited, so every result is
        // unchanged.)
        if (!(op instanceof Function func) || !func.isSkolemConstant()) {
            return -1;
        }

        final Map<Operator, Integer> introductionTimeCache =
            goal.proof().getServices().getCaches().getIntroductionTimeCache();

        // ConcurrentLruCache: get/put are individually atomic, no external lock needed.
        Integer res = introductionTimeCache.get(op);

        if (res == null) {
            res = introductionTimeHelp(op, goal);
            // Do NOT cache the "not introduced (yet)" answer (-1): op may be introduced by a later
            // rule application, after which introductionTimeHelp would find a real time. Caching
            // the -1 would freeze it, making the value depend on whether op happened to be first
            // queried before or after its introduction -- i.e. on the access pattern (which
            // features run, when). That makes term ordering, and hence OneStepSimplifier rewriting,
            // subtly non-deterministic. A real introduction time, once found, is stable (the
            // introducing rule stays in the applied-rule prefix), so it is safe to cache.
            if (res != -1) {
                introductionTimeCache.put(op, res);
            }
        }

        return res;
    }

    private int introductionTimeHelp(Operator op, Goal goal) {
        ImmutableList<RuleApp> appliedRules = goal.appliedRuleApps();
        while (!appliedRules.isEmpty()) {
            final RuleApp app = appliedRules.head();
            appliedRules = appliedRules.tail();

            if (app instanceof TacletApp tapp) {
                if (!inNewSmallSymRuleSet(tapp)) {
                    continue;
                }

                if (introducesSkolemSymbol(tapp, op)) {
                    return appliedRules.size();
                }
            }
        }

        return -1;
    }

    private boolean introducesSkolemSymbol(TacletApp tapp, Operator op) {
        for (final var entry : tapp.instantiations().getInstantiationMap()) {
            if (!(entry.key() instanceof SkolemTermSV)) {
                continue;
            }
            if (op == ((Term) entry.value().getInstantiation()).op()) {
                return true;
            }
        }
        return false;
    }

    private boolean inNewSmallSymRuleSet(TacletApp tapp) {
        ImmutableList<RuleSet> ruleSets = tapp.taclet().getRuleSets();
        while (!ruleSets.isEmpty()) {
            final RuleSet rs = ruleSets.head();
            ruleSets = ruleSets.tail();
            if (rs.name().equals(newSymRuleSetName)) {
                return true;
            }
        }
        return false;
    }

    protected ImmutableList<Term> collectAtoms(Term t) {
        final AtomCollector m = new AtomCollector();
        m.collect(t);
        return m.getResult();
    }

    private class AtomCollector extends Collector {
        protected void collect(Term te) {
            if (te.op() == mul) {
                collect(te.sub(0));
                collect(te.sub(1));
            } else {
                addTerm(te);
            }
        }
    }
}
