package de.uka.ilkd.key.scripts;

import org.jspecify.annotations.Nullable;
import org.key_project.prover.rules.Rule;
import de.uka.ilkd.key.macros.FilterStrategy;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.strategy.Strategy;
import org.key_project.logic.Name;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.util.collection.Pair;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;

class AdditionalRulesStrategy extends FilterStrategy {
    /** Name of that strategy */
    private static final Name NAME = new Name(
            AdditionalRulesStrategy.class.getSimpleName());

    private static final Map<String, String> TRANSLATIONS =
            Map.of("high", "-50", "medium", "1000", "low", "10000");
    private static final int DEFAULT_PRIORITY = 1000;

    private final List<Pair<String, Integer>> additionalRules;
    private final boolean exclusive;

    public AdditionalRulesStrategy(Strategy delegate, String additionalRules, boolean exclusive) {
        super(delegate);
        this.additionalRules = parseAddRules(additionalRules);
        this.exclusive = exclusive;
    }

    private List<Pair<String, Integer>> parseAddRules(String additionalRules) {
        List<Pair<String, Integer>> result = new ArrayList<>();
        for (String entry : additionalRules.trim().split(" *, *")) {
            String[] parts = entry.split(" *= *", 2);
            int prio;
            if (parts.length == 2) {
                String prioStr = parts[1];
                prioStr = TRANSLATIONS.getOrDefault(prioStr, prioStr);
                try {
                    prio = Integer.parseInt(prioStr);
                } catch (NumberFormatException e) {
                    throw new IllegalArgumentException("Invalid value for additional rule: " + parts[1]);
                }
            } else {
                prio = DEFAULT_PRIORITY;
            }

            result.add(new Pair<>(parts[0], prio));
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
        if (exclusive) {
            return false;
        } else {
            return super.isApprovedApp(app, pio, goal);
        }
    }

    private @Nullable RuleAppCost computeLocalCost(Rule rule) {
        String name = rule.name().toString();
        Optional<Integer> cost = lookup(name);
        if(cost.isPresent()) {
            return NumberRuleAppCost.create(cost.get());
        }

        if (rule instanceof Taclet taclet) {
            for (RuleSet rs : taclet.getRuleSets()) {
                String rname = rs.name().toString();
                cost = lookup(rname);
                if(cost.isPresent()) {
                    return NumberRuleAppCost.create(cost.get());
                }
            }
        }

        return null;
    }

    private Optional<Integer> lookup(String name) {
        return additionalRules.stream()
                .filter(nameAndPrio -> name.matches(nameAndPrio.first))
                .findFirst()
                .map(p -> p.second);
    }

    @Override
    public boolean isStopAtFirstNonCloseableGoal() {
        return false;
    }


}