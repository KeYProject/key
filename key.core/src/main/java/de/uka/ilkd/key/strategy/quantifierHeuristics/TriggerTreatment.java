/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.EnumSet;
import java.util.Set;

import de.uka.ilkd.key.strategy.StrategyProperties;

/**
 * How much the quantifier instantiation heuristic is told about the theories, as the strategy's
 * trigger option selects it.
 *
 * A treatment is a set of admitted instance {@link Origin}s and a choice of theory supports.
 * Which theories select the triggers follows {@link #isClassic()}; whether an instance found by
 * some mechanism is offered at all follows {@link #admits(Origin)}. A new mechanism is one new
 * origin, admitted here per treatment.
 *
 * The solved-position origin is admitted everywhere: solving happens inside the structural
 * matching of the formula's own triggers, which every treatment runs (see
 * {@code BasicMatching}).
 */
public enum TriggerTreatment {

    /** Everything the heuristic knows. */
    BEST(EnumSet.allOf(Origin.class)),

    /** The theories' trigger selection, with theory-provided triggers unified only. */
    GOOD(EnumSet.of(Origin.OWN_PATTERN, Origin.SOLVED_POSITION, Origin.THEORY_UNIFIED,
        Origin.THEORY_DIRECT)),

    /** Equality and integer rejection only, and no ordering of the candidates. */
    CLASSIC(EnumSet.of(Origin.OWN_PATTERN, Origin.SOLVED_POSITION));

    private final Set<Origin> admittedOrigins;

    TriggerTreatment(Set<Origin> admittedOrigins) {
        this.admittedOrigins = admittedOrigins;
    }

    public static TriggerTreatment forOption(String option) {
        if (StrategyProperties.TRIGGERS_CLASSIC.equals(option)) {
            return CLASSIC;
        }
        return StrategyProperties.TRIGGERS_GOOD.equals(option) ? GOOD : BEST;
    }

    /** Whether only the classic supports are consulted, and candidates are left unordered. */
    public boolean isClassic() {
        return this == CLASSIC;
    }

    /** Whether an instance of the given origin is offered under this treatment. */
    boolean admits(Origin origin) {
        return admittedOrigins.contains(origin);
    }
}
