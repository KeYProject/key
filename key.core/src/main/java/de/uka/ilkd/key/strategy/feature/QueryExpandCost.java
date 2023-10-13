/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.rule.QueryExpand;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;

import org.key_project.util.collection.ImmutableList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * A Feature that computes the cost for using the query expand rule.
 *
 * @author gladisch
 */
public class QueryExpandCost implements Feature {
    private static final Logger LOGGER = LoggerFactory.getLogger(QueryExpandCost.class);

    /** Constant that represents the boolean value true */
    public static final RuleAppCost ZERO_COST = NumberRuleAppCost.getZeroCost();
    /** Constant that represents the boolean value false */
    public static final RuleAppCost TOP_COST = TopRuleAppCost.INSTANCE;

    /**
     * If the literals in a query become greater than abs(ConsideredAsBigLiteral), then this is
     * interpreted as a "loop smell", i.e. the proof construction is in a loop and produces big
     * literals.
     */
    public static final int CONSIDERED_AS_BIG_LITERAL = 7;

    /**
     * The base cost for this rule.
     */
    private final int baseCost;
    private final int maxRepetitionsOnSameTerm;
    private final int termAgeFactor;
    private final boolean useExperimentalHeuristics;

    /**
     * @param baseCost Should be set to 200. This was the cost before this class was introduced.
     * @param maxRepetitionsOnSameTerm Search in the current branch if query expand has been already
     *        applied on this term. For each such application a penalty cost is added. If this limit
     *        is exceeded the cost is set to TOP_COST, i.e. the rule is not applied.
     * @param termAgeFactor This factor (must be >= 0) sets the cost of older queries lower, than
     *        that of younger queries (i.e. that occur later in proofs). The effect is a
     *        breath-first search on the expansion of queries. In class <code>QueryExpand</code> the
     *        time is stored, when queries can be expanded for the first time.
     * @param useExperimentalHeuristics Activates experimental, pattern-based heuristics.
     */
    public QueryExpandCost(int baseCost, int maxRepetitionsOnSameTerm, int termAgeFactor,
            boolean useExperimentalHeuristics) {
        super();
        this.baseCost = baseCost;
        this.maxRepetitionsOnSameTerm = maxRepetitionsOnSameTerm;
        this.termAgeFactor = termAgeFactor;
        this.useExperimentalHeuristics = useExperimentalHeuristics;
    }

    @Override
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal) {
        final Services services = goal.proof().getServices();
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        final Term t = pos.subTerm();

        long cost = baseCost;

        if (useExperimentalHeuristics) {
            // If the factor is too small, then higher cost has no effect for some reason.
            int litcost = maxIntliteralInArgumentsTimesTwo(t, integerLDT, services);
            if (litcost > CONSIDERED_AS_BIG_LITERAL * 2) {
                return TOP_COST;
            }
        }

        if (maxRepetitionsOnSameTerm != -1 && maxRepetitionsOnSameTerm < Integer.MAX_VALUE) {
            int count = queryExpandAlreadyAppliedAtPos(app, pos, goal);
            if (count > maxRepetitionsOnSameTerm) {
                return TOP_COST;
            } else {
                cost += count * 2000L;
            }
        }

        if (termAgeFactor > 0) {
            Long qtime = QueryExpand.INSTANCE.getTimeOfQuery(t);
            if (qtime != null) {
                cost += qtime * termAgeFactor;
            } else {
                LOGGER.info("QueryExpandCost::compute. Time of query should have been set already."
                    + "The query was: {}", t);
            }
        }

        return NumberRuleAppCost.create(cost);
    }

    /**
     * @param t the query that is considered for the rule expand query.
     * @return Cost that is computed base on the integer literals occurring in the numerical
     *         arguments of the query t.
     */
    private static int maxIntliteralInArgumentsTimesTwo(Term t, IntegerLDT iLDT, Services serv) {
        final Namespace<Sort> sorts = serv.getNamespaces().sorts();
        final Sort intSort = sorts.lookup(IntegerLDT.NAME);
        int cost = 0;
        // The computation is limited to arguments that have an arithmetic type.
        // E.g., don't calculate int literals in the heap parameter.
        for (int i = 0; i < t.arity(); i++) {
            Term arg = t.sub(i);
            if (arg.sort() == intSort) {
                cost = Math.max(cost, sumOfAbsLiteralsTimesTwo(arg, iLDT, serv));
            }
        }
        return cost;
    }

    /**
     * Absolute values of literal occurring in t a used for cost computation. The cost of literals
     * is sorted the following way:0,1,-1,2,-2,3,-3,...
     *
     * @param t The term is expected to be an argument of the query.
     * @return Sum* of the absolute values of integer literals occurring in t multiplied by two. (*)
     *         The sum is modified by extrapolating negative numbers from zero by one. The cost of a
     *         query f(n-1) a slightly higher cost than the cost of f(n+1).
     */
    private static int sumOfAbsLiteralsTimesTwo(Term t, IntegerLDT iLDT, Services serv) {
        if (t.op() == iLDT.getNumberSymbol()) {
            String strVal = AbstractTermTransformer.convertToDecimalString(t, serv);
            int val = Integer.parseInt(strVal);
            if (val >= 0) {
                return val * 2;
            } else {
                // Negative numbers get a slightly higher cost than positive numbers.
                return (val * -2) + 1;
            }
        } else {
            int sum = 0;
            for (int i = 0; i < t.arity(); i++) {
                sum += sumOfAbsLiteralsTimesTwo(t.sub(i), iLDT, serv);
            }
            return sum;
        }
    }

    /**
     * The method checks if the same rule has been applied earlier on this branch at the same
     * position in the sequent. This method detects repetitive rule applications and is used to
     * prevent loops in the proof tree.
     *
     * @param app The rule application.
     * @param pos The occurrence position.
     * @param goal The goal.
     * @return The number of repetitive rule applications.
     */
    protected int queryExpandAlreadyAppliedAtPos(RuleApp app, PosInOccurrence pos, Goal goal) {
        int count = 0;
        ImmutableList<RuleApp> appliedRuleApps = goal.appliedRuleApps();
        if (appliedRuleApps != null && !appliedRuleApps.isEmpty()) {
            for (RuleApp appliedRuleApp : appliedRuleApps) {
                final PosInOccurrence pio = appliedRuleApp.posInOccurrence();
                if (pio != null) {
                    final Term oldterm = pio.subTerm();
                    final Term curterm = pos.subTerm();
                    if (appliedRuleApp.rule().equals(QueryExpand.INSTANCE)
                            && oldterm.equalsModIrrelevantTermLabels(curterm)) {
                        count++;
                        if (count > maxRepetitionsOnSameTerm) {
                            break;
                        }
                    }
                }
            }
        }
        return count;
    }

    /**
     * This method determines whether the given goal belongs to a subtree of a step case or body
     * preserves case. The search is done recursively for all parent nodes until either there are no
     * more parent nodes or we have found an according (or opposing) branch label.
     *
     * @param goal the current proof goal
     * @return a boolean saying whether the goal belongs to a step case
     */
    protected static boolean isStepCaseBranch(Goal goal) {
        Node node = goal.node();
        while (node != null) {
            NodeInfo ni = node.getNodeInfo();
            if (ni != null && ni.getBranchLabel() != null) {
                String branchName = ni.getBranchLabel().toLowerCase();
                if (branchName.contains("step case") || branchName.contains("body preserves")) {
                    return true;
                } else if (branchName.contains("base case")
                        || branchName.contains("invariant initially")
                        || branchName.contains("use case")) {
                    return false;
                }
            }
            node = node.parent();
        }
        return false;
    }

    public int getMaxRepetitionsOnSameTerm() {
        return maxRepetitionsOnSameTerm;
    }
}
