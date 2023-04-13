package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.java.ServiceCaches;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;


/**
 * Feature that returns the maximum number of literals occurring within a d-path of the find-formula
 * as a formula of the antecedent. Used terminology is defined in Diss. by Martin Giese.
 */
public class CountMaxDPathFeature extends AbstractBetaFeature {

    public final static Feature INSTANCE = new CountMaxDPathFeature();

    private CountMaxDPathFeature() {}

    @Override
    protected long doComputation(PosInOccurrence pos, Term findTerm, ServiceCaches caches) {
        return maxDPath(findTerm, !pos.isInAntec(), caches);
    }

}
