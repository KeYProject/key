/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.Debug;

import org.key_project.logic.PosInTerm;
import org.key_project.logic.Term;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.instantiation.AssumesFormulaInstSeq;
import org.key_project.prover.rules.instantiation.AssumesFormulaInstantiation;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;

/**
 * Container for RuleApp instances with cost as determined by a given Strategy. Instances of this
 * class are immutable.
 */
public abstract class RuleAppContainer implements Comparable<RuleAppContainer> {

    /**
     * The stored rule app
     */
    private final RuleApp ruleApp;

    /**
     * The costs of the stored rule app
     */
    private final RuleAppCost cost;

    protected RuleAppContainer(RuleApp p_app, RuleAppCost p_cost) {
        ruleApp = p_app;
        cost = p_cost;
    }

    @Override
    public final int compareTo(RuleAppContainer o) {
        final int byCost = cost.compareTo(o.cost);
        if (byCost != 0) {
            return byCost;
        }
        // Equal cost: order deterministically by content so the proof search does not depend on the
        // (timing-dependent) order in which candidates were generated/selected -- the source of
        // run-to-run proof variance under concurrent goal processing. Uses only stable keys (rule,
        // operator and schema-variable names; structural positions and instantiations); never
        // object hashCodes or toString(), which can embed identity (e.g. term-label hashes).
        return compareByContent(ruleApp, o.ruleApp);
    }

    private static int compareByContent(RuleApp a, RuleApp b) {
        if (a == b) {
            return 0;
        }
        int c = a.rule().name().compareTo(b.rule().name());
        if (c != 0) {
            return c;
        }
        c = comparePos(a.posInOccurrence(), b.posInOccurrence());
        if (c != 0) {
            return c;
        }
        // Same rule and focus: distinguish by instantiations (e.g. two applyEq on different eqs).
        if (a instanceof TacletApp ta && b instanceof TacletApp tb) {
            c = compareInstantiations(ta, tb);
            if (c != 0) {
                return c;
            }
            return compareAssumesInstantiations(ta, tb);
        }
        return 0;
    }

    /**
     * Compare the {@code \assumes} instantiations of two taclet apps. These are kept separately
     * from the schema-variable map, so two apps of the same taclet at the same focus that use
     * different assumes-formulas (e.g. {@code applyEq} instances rewriting with two different
     * equations) are still tied after {@link #compareInstantiations}; without this comparison the
     * queue order of such candidates — and thereby proof search — would depend on the
     * (history-dependent) order in which they were inserted into the queue.
     */
    private static int compareAssumesInstantiations(TacletApp a, TacletApp b) {
        final ImmutableList<AssumesFormulaInstantiation> ia = a.assumesFormulaInstantiations();
        final ImmutableList<AssumesFormulaInstantiation> ib = b.assumesFormulaInstantiations();
        if (ia == ib) {
            return 0;
        }
        if (ia == null) {
            return -1;
        }
        if (ib == null) {
            return 1;
        }
        int c = Integer.compare(ia.size(), ib.size());
        if (c != 0) {
            return c;
        }
        final var ita = ia.iterator();
        final var itb = ib.iterator();
        while (ita.hasNext()) {
            final AssumesFormulaInstantiation fa = ita.next();
            final AssumesFormulaInstantiation fb = itb.next();
            final boolean seqA = fa instanceof AssumesFormulaInstSeq;
            final boolean seqB = fb instanceof AssumesFormulaInstSeq;
            c = Boolean.compare(seqA, seqB);
            if (c != 0) {
                return c;
            }
            if (seqA) {
                c = Boolean.compare(((AssumesFormulaInstSeq) fa).inAntecedent(),
                    ((AssumesFormulaInstSeq) fb).inAntecedent());
                if (c != 0) {
                    return c;
                }
            }
            c = compareByName(fa.getSequentFormula().formula(), fb.getSequentFormula().formula());
            if (c != 0) {
                return c;
            }
        }
        return 0;
    }

    private static int comparePos(PosInOccurrence a, PosInOccurrence b) {
        if (a == b) {
            return 0;
        }
        if (a == null) {
            return -1;
        }
        if (b == null) {
            return 1;
        }
        int c = Boolean.compare(a.isInAntec(), b.isInAntec());
        if (c != 0) {
            return c;
        }
        final PosInTerm pa = a.posInTerm();
        final PosInTerm pb = b.posInTerm();
        final int n = Math.min(pa.depth(), pb.depth());
        for (int i = 0; i < n; i++) {
            c = Integer.compare(pa.getIndexAt(i), pb.getIndexAt(i));
            if (c != 0) {
                return c;
            }
        }
        c = Integer.compare(pa.depth(), pb.depth());
        if (c != 0) {
            return c;
        }
        // Same path: if it is literally the same formula, no need to walk it.
        if (a.sequentFormula() == b.sequentFormula()) {
            return 0;
        }
        return compareByName(a.sequentFormula().formula(), b.sequentFormula().formula());
    }

    private static int compareInstantiations(TacletApp a, TacletApp b) {
        final var ma = a.instantiations().getInstantiationMap();
        final var mb = b.instantiations().getInstantiationMap();
        if (ma == mb) {
            return 0;
        }
        final var ia = ma.iterator();
        final var ib = mb.iterator();
        while (ia.hasNext() && ib.hasNext()) {
            final var ea = ia.next();
            final var eb = ib.next();
            int c = ea.key().name().compareTo(eb.key().name());
            if (c != 0) {
                return c;
            }
            c = compareInstValue(ea.value().getInstantiation(), eb.value().getInstantiation());
            if (c != 0) {
                return c;
            }
        }
        return Boolean.compare(ia.hasNext(), ib.hasNext());
    }

    private static int compareInstValue(Object va, Object vb) {
        if (va instanceof Term ta && vb instanceof Term tb) {
            return compareByName(ta, tb);
        }
        if (va == vb) {
            return 0;
        }
        return String.valueOf(va).compareTo(String.valueOf(vb));
    }

    /** Structural order on terms by operator names only -- stable across runs (unlike hashCode). */
    private static int compareByName(Term a, Term b) {
        int c = a.op().name().compareTo(b.op().name());
        if (c != 0) {
            return c;
        }
        c = Integer.compare(a.arity(), b.arity());
        if (c != 0) {
            return c;
        }
        for (int i = 0; i < a.arity(); i++) {
            c = compareByName(a.sub(i), b.sub(i));
            if (c != 0) {
                return c;
            }
        }
        return 0;
    }

    /**
     * Create a list of new RuleAppContainers that are to be considered for application.
     */
    public abstract ImmutableList<RuleAppContainer> createFurtherApps(Goal p_goal);

    /**
     * Create a <code>RuleApp</code> that is suitable to be applied or <code>null</code>.
     */
    public abstract RuleApp completeRuleApp(Goal p_goal);

    protected final RuleApp getRuleApp() {
        return ruleApp;
    }


    public final RuleAppCost getCost() {
        return cost;
    }

    /**
     * Add the goal-age term to a strategy-computed cost. Age (the goal time, i.e. number of rules
     * applied so far) is a single first-class component of every container's cost, contributed here
     * rather than inside any {@link de.uka.ilkd.key.strategy.Strategy#computeCost} -- so a strategy
     * (and each of its components) computes only its age-free cost, and age is added exactly once
     * per queued container regardless of how strategies are composed. {@code Top} stays
     * {@code Top}.
     */
    protected static RuleAppCost withAge(RuleAppCost ageFreeCost, Goal goal) {
        return ageFreeCost.add(NumberRuleAppCost.create(goal.getTime()));
    }

    /**
     * Create container for a RuleApp.
     *
     * @return container for the currently applicable RuleApp, the cost may be an instance of
     *         <code>TopRuleAppCost</code>.
     */
    public static @NonNull RuleAppContainer createAppContainer(
            RuleApp p_app,
            PosInOccurrence p_pio,
            Goal p_goal) {

        if (p_app instanceof NoPosTacletApp) {
            return TacletAppContainer.createAppContainers((NoPosTacletApp) p_app, p_pio, p_goal);
        }

        if (p_app instanceof IBuiltInRuleApp) {
            return BuiltInRuleAppContainer.createAppContainer((IBuiltInRuleApp) p_app, p_pio,
                p_goal);
        }

        Debug.fail("Unexpected kind of rule.");

        return null;
    }

    /**
     * Create containers for RuleApps.
     *
     * @return list of containers for the currently applicable RuleApps, the cost may be an instance
     *         of <code>TopRuleAppCost</code>.
     */
    public static ImmutableList<RuleAppContainer> createAppContainers(
            ImmutableList<? extends RuleApp> rules,
            PosInOccurrence pos, Goal goal) {
        ImmutableList<RuleAppContainer> result = ImmutableList.nil();

        if (rules.size() == 1) {
            result = result.prepend(createAppContainer(rules.head(), pos, goal));
        } else if (rules.size() > 1) {
            ImmutableList<NoPosTacletApp> tacletApplications =
                ImmutableList.nil();
            ImmutableList<IBuiltInRuleApp> builtInRuleApplications =
                ImmutableList.nil();

            for (RuleApp rule : rules) {
                if (rule instanceof NoPosTacletApp) {
                    tacletApplications = tacletApplications.prepend((NoPosTacletApp) rule);
                } else {
                    builtInRuleApplications =
                        builtInRuleApplications.prepend((IBuiltInRuleApp) rule);
                }
            }

            if (!builtInRuleApplications.isEmpty()) {
                result = result.append(BuiltInRuleAppContainer
                        .createInitialAppContainers(builtInRuleApplications, pos, goal));
            }
            result = result.prepend(
                TacletAppContainer.createInitialAppContainers(tacletApplications, pos, goal));
        }
        return result;
    }

}
