/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.*;

import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.strategy.ComponentStrategy.StrategyAspect;

import org.key_project.logic.Name;
import org.key_project.prover.rules.Rule;
import org.key_project.prover.rules.RuleSet;

/// A cache for the strategies responsible for a given [Rule] and [RuleSet].
public class ResponsibleStrategyCache {
    // map rulesets to the strategies that participate in their cost computations, instantiation or
    // approval decisions
    private final Map<RuleSet, List<ComponentStrategy>> costResponsibilityMap =
        new LinkedHashMap<RuleSet, List<ComponentStrategy>>();
    private final Map<RuleSet, List<ComponentStrategy>> instantiationResponsibilityMap =
        new LinkedHashMap<RuleSet, List<ComponentStrategy>>();
    private final Map<RuleSet, List<ComponentStrategy>> approvalResponsibilityMap =
        new LinkedHashMap<RuleSet, List<ComponentStrategy>>();
    // map rules to the strategies that participate in their cost computations, instantiation or
    // approval decisions
    private final Map<Rule, LinkedHashSet<ComponentStrategy>> costRuleToStrategyMap =
        new LinkedHashMap<Rule, LinkedHashSet<ComponentStrategy>>();
    private final Map<Rule, LinkedHashSet<ComponentStrategy>> instantiationRuleToStrategyMap =
        new LinkedHashMap<Rule, LinkedHashSet<ComponentStrategy>>();
    private final Map<Rule, LinkedHashSet<ComponentStrategy>> approvalRuleToStrategyMap =
        new LinkedHashMap<Rule, LinkedHashSet<ComponentStrategy>>();
    private final Map<Name, ComponentStrategy> nameToStrategyMap =
        new HashMap<Name, ComponentStrategy>();

    public ResponsibleStrategyCache(List<ComponentStrategy> strategies) {
        initialize(StrategyAspect.Cost, strategies);
        initialize(StrategyAspect.Instantiation, strategies);
        initialize(StrategyAspect.Approval, strategies);
    }

    /**
     * Caches the information which strategies are responsible for which ruleset
     *
     * @param aspect the StrategyAspect for which the cache is created
     * @param strategies list of all component strategies
     */
    private void initialize(StrategyAspect aspect, List<ComponentStrategy> strategies) {
        var map = getResponsibilityMap(aspect);
        for (ComponentStrategy strategy : strategies) {
            nameToStrategyMap.put(strategy.name(), strategy);
            var res = strategy.getResponsibilities(aspect);
            for (var rs : res) {
                map.computeIfAbsent(rs, k -> new ArrayList<>()).add(strategy);
            }
        }
    }

    /// Returns the map for the given aspect
    private Map<Rule, LinkedHashSet<ComponentStrategy>> getRuleToStrategyMap(
            StrategyAspect aspect) {
        return switch (aspect) {
            case Cost -> costRuleToStrategyMap;
            case Instantiation -> instantiationRuleToStrategyMap;
            case Approval -> approvalRuleToStrategyMap;
        };
    }

    /// Returns the map for the given aspect
    private Map<RuleSet, List<ComponentStrategy>> getResponsibilityMap(StrategyAspect aspect) {
        return switch (aspect) {
            case Cost -> costResponsibilityMap;
            case Instantiation -> instantiationResponsibilityMap;
            case Approval -> approvalResponsibilityMap;
        };
    }

    /// Returns the strategies responsible for the given [Rule] under the given [StrategyAspect].
    public LinkedHashSet<ComponentStrategy> getResponsibleStrategies(Rule rule,
            List<ComponentStrategy> strategies, StrategyAspect aspect) {
        var ruleToStrategyMap = getRuleToStrategyMap(aspect);
        LinkedHashSet<ComponentStrategy> strats = ruleToStrategyMap.get(rule);
        if (strats == null) {
            strats = new LinkedHashSet<>();
            if (rule instanceof BuiltInRule bir) {
                for (var cs : strategies) {
                    if (cs.isResponsibleFor(bir)) {
                        strats.add(cs);
                    }
                }
            } else {
                var ruleSets = rule.ruleSets();
                Map<RuleSet, List<ComponentStrategy>> responsibilityMap =
                    getResponsibilityMap(aspect);
                while (ruleSets.hasNext()) {
                    var rs = ruleSets.next();
                    List<ComponentStrategy> s = responsibilityMap.get(rs);
                    if (s != null)
                        strats.addAll(s);
                }
            }
            ruleToStrategyMap.put(rule, strats);
        }
        return strats;
    }

    /// Returns the strategy with the given [Name]
    public ComponentStrategy getStrategyByName(Name name) {
        return nameToStrategyMap.get(name);
    }
}
