/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import java.util.Map;

import de.uka.ilkd.key.logic.op.SkolemTermSV;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.ldt.IIntLdt;
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


    protected AbstractMonomialSmallerThanFeature(IIntLdt numbers) {
        this.add = numbers.getAdd();
        this.mul = numbers.getMul();
        this.Z = numbers.getNumberSymbol();
    }

    /**
     * if {@code op} is a Skolem constant the returned introduction time is the number of taclets
     * applied before and including the taclet by which its was introduced. <ctrong>For all other
     * operators the returned value is -1</strong>
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
