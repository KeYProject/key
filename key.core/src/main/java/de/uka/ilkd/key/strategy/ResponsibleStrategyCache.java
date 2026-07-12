/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.*;
import java.util.concurrent.ConcurrentHashMap;

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
    // Map rules to the strategies that participate in their cost computations, instantiation or
    // approval decisions. These are filled lazily on the first query for a rule. One strategy
    // object is shared by all goals of a proof, so under the multi-core prover several worker
    // threads query and fill these maps at the same time; they are therefore concurrent maps
    // filled through computeIfAbsent (atomic per rule). The responsible-strategy set of a rule is
    // a pure function of the rule, so the cached value is the same whichever worker computes it --
    // the result stays reproducible. A plain map here corrupts under concurrent writes and made
    // the strategy return an inconsistent set between two evaluations of the same feature term,
    // which broke the BackTrackingManager's determinism check (a worker AssertionError).
    private final Map<Rule, LinkedHashSet<ComponentStrategy>> costRuleToStrategyMap =
        new ConcurrentHashMap<>();
    private final Map<Rule, LinkedHashSet<ComponentStrategy>> instantiationRuleToStrategyMap =
        new ConcurrentHashMap<>();
    private final Map<Rule, LinkedHashSet<ComponentStrategy>> approvalRuleToStrategyMap =
        new ConcurrentHashMap<>();
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
        // computeIfAbsent fills the entry atomically: concurrent workers proving different goals
        // of the same proof never see a half-built map or overwrite each other. The mapping
        // function only reads the responsibility maps (built once in the constructor, read-only
        // afterwards) and the strategies list, so it is a pure function of the rule.
        return ruleToStrategyMap.computeIfAbsent(rule, r -> {
            LinkedHashSet<ComponentStrategy> strats = new LinkedHashSet<>();
            if (r instanceof BuiltInRule bir) {
                for (var cs : strategies) {
                    if (cs.isResponsibleFor(bir)) {
                        strats.add(cs);
                    }
                }
            } else {
                var ruleSets = r.ruleSets();
                Map<RuleSet, List<ComponentStrategy>> responsibilityMap =
                    getResponsibilityMap(aspect);
                while (ruleSets.hasNext()) {
                    var rs = ruleSets.next();
                    List<ComponentStrategy> s = responsibilityMap.get(rs);
                    if (s != null) {
                        strats.addAll(s);
                    }
                }
            }
            return strats;
        });
    }

    /// Returns the strategy with the given [Name]
    public ComponentStrategy getStrategyByName(Name name) {
        return nameToStrategyMap.get(name);
    }
}
