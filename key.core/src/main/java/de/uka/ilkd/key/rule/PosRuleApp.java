package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.PosInOccurrence;

/**
 * Interface for rule applications with associated position information.
 *
 * @author Arne Keller
 */
public interface PosRuleApp {
    /**
     * @return the position the rule was applied on
     */
    PosInOccurrence posInOccurrence();
}
