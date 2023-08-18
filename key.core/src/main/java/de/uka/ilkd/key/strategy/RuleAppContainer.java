/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.Debug;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

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
        return cost.compareTo(o.cost);
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
     * Create container for a RuleApp.
     *
     * @return container for the currently applicable RuleApp, the cost may be an instance of
     *         <code>TopRuleAppCost</code>.
     */
    public static RuleAppContainer createAppContainer(RuleApp p_app, PosInOccurrence p_pio,
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
            ImmutableList<? extends RuleApp> rules, PosInOccurrence pos, Goal goal) {
        ImmutableList<RuleAppContainer> result = ImmutableSLList.nil();

        if (rules.size() == 1) {
            result = result.prepend(createAppContainer(rules.head(), pos, goal));
        } else if (rules.size() > 1) {
            ImmutableList<NoPosTacletApp> tacletApplications =
                ImmutableSLList.nil();
            ImmutableList<IBuiltInRuleApp> builtInRuleApplications =
                ImmutableSLList.nil();

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

    @Override
    public String toString() {
        return "RuleAppContainer{" +
            "ruleApp=" + ruleApp.rule().name() +
            ", cost=" + cost +
            '}';
    }
}
