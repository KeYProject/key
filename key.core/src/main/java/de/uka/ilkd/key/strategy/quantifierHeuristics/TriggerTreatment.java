/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.strategy.StrategyProperties;

/**
 * How much the quantifier instantiation heuristic is told about the theories, as the strategy's
 * trigger option selects it.
 */
public enum TriggerTreatment {

    /** Everything the heuristic knows. */
    BEST,

    /** The theories' trigger selection, with theory-provided triggers unified only. */
    GOOD,

    /** Equality and integer rejection only, and no ordering of the candidates. */
    CLASSIC;

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

    /**
     * Whether a theory-provided trigger may also be matched by {@link BasicMatching}, and not only
     * unified.
     *
     * Basic matching binds the trigger's metavariable to a term the trigger never read, so a
     * trigger written for one heap matches a read over another, and a theory can solve an array
     * index along the way. It is the one part of the heuristic that instantiates from a term the
     * formula does not name, so it is left to the most informed treatment.
     */
    public boolean allowsBasicMatchingOfTheoryTriggers() {
        return this == BEST;
    }
}
