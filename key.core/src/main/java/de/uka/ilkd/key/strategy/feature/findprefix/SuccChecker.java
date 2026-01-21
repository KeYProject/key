package de.uka.ilkd.key.strategy.feature.findprefix;

import de.uka.ilkd.key.logic.PosInOccurrence;

/**
 * Checks, whether the position in occurrence is in the succedent.
 *
 * @author christoph
 */
class SuccChecker implements Checker {

    @Override
    public boolean check(PosInOccurrence pio) {
        return !pio.isInAntec();
    }

}
