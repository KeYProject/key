package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.FilterStrategy;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.Strategy;

import java.util.HashMap;
import java.util.Map;

class AdditionalRulesStrategy extends FilterStrategy {
    /** Name of that strategy */
    private static final Name NAME = new Name(
            AdditionalRulesStrategy.class.getSimpleName());

    private static final Map<String, String> TRANSLATIONS =
            Map.of("high", "-50", "medium", "1000", "low", "10000");

    private final Map<String, Integer> additionalRules;

    public AdditionalRulesStrategy(Strategy delegate,
                                   Map<String, String> additionalRules) {
        super(delegate);
        this.additionalRules = parseAddRules(additionalRules);
    }

    private Map<String, Integer> parseAddRules(Map<String, String> additionalRules) {
        Map<String, Integer> result = new HashMap<>();
        for (Map.Entry<String, String> entry : additionalRules.entrySet()) {
            String value = TRANSLATIONS.getOrDefault(entry.getValue(), entry.getValue());
            try {
                result.put(entry.getKey(), Integer.parseInt(value));
            } catch (NumberFormatException e) {
                throw new IllegalArgumentException("Invalid value for additional rule: " + entry.getKey());
            }
        }
        return result;
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pio, Goal goal) {
        RuleAppCost localCost = computeLocalCost(app.rule());
        if (localCost != null) {
            return localCost;
        }
        return super.computeCost(app, pio, goal);
    }

    @Override
    public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
        RuleAppCost localCost = computeLocalCost(app.rule());
        if (localCost != null) {
            return true;
        }
        return super.isApprovedApp(app, pio, goal);
    }

    private RuleAppCost computeLocalCost(Rule rule) {
        String name = rule.name().toString();
        Integer cost = additionalRules.get(name);
        if(cost != null) {
            return NumberRuleAppCost.create(cost);
        }

        if (rule instanceof Taclet) {
            Taclet taclet = (Taclet) rule;
            for (RuleSet rs : taclet.getRuleSets()) {
                String rname = rs.name().toString();
                Integer rcost = additionalRules.get(rname);
                if(rcost != null) {
                    return NumberRuleAppCost.create(rcost);
                }
            }
        }

        return null;
    }

    @Override
    public boolean isStopAtFirstNonCloseableGoal() {
        return false;
    }


}