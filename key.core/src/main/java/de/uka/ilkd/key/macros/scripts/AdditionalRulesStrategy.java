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
import de.uka.ilkd.key.strategy.TopRuleAppCost;

import java.util.HashMap;
import java.util.Map;

class AdditionalRulesStrategy extends FilterStrategy {
    /** Name of that strategy */
    private static final Name NAME = new Name(
            AdditionalRulesStrategy.class.getSimpleName());

    private static final Map<String, String> TRANSLATIONS =
            Map.of("high", "-50", "medium", "1000", "low", "10000");

    private final Map<String, RuleAppCost> additionalRules;

    public AdditionalRulesStrategy(Strategy delegate,
                                   Map<String, String> additionalRules) {
        super(delegate);
        this.additionalRules = parseAddRules(additionalRules);
    }

    private Map<String, RuleAppCost> parseAddRules(Map<String, String> additionalRules) {
        Map<String, RuleAppCost> result = new HashMap<>();
        for (Map.Entry<String, String> entry : additionalRules.entrySet()) {
            String value = TRANSLATIONS.getOrDefault(entry.getValue(), entry.getValue());
            try {
                if(value.equals("off")) {
                    result.put(entry.getKey(), TopRuleAppCost.INSTANCE);
                } else {
                    int parsed = Integer.parseInt(value);
                    result.put(entry.getKey(), NumberRuleAppCost.create(parsed));
                }
            } catch (NumberFormatException e) {
                throw new IllegalArgumentException("Invalid value for rule cost: " + value);
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
            return localCost != TopRuleAppCost.INSTANCE;
        }
        return super.isApprovedApp(app, pio, goal);
    }

    private RuleAppCost computeLocalCost(Rule rule) {
        String name = rule.name().toString();
        RuleAppCost cost = additionalRules.get(name);
        if(cost != null) {
            return cost;
        }

        if (rule instanceof Taclet) {
            Taclet taclet = (Taclet) rule;
            for (RuleSet rs : taclet.getRuleSets()) {
                String rname = rs.name().toString();
                RuleAppCost rcost = additionalRules.get(rname);
                if(rcost != null) {
                    return rcost;
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