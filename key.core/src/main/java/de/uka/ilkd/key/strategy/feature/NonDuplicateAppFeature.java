package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;



/**
 * Binary feature that returns zero iff a certain Taclet app has not already been performed
 */
public class NonDuplicateAppFeature extends AbstractNonDuplicateAppFeature {

    public static final Feature INSTANCE = new NonDuplicateAppFeature();

    public boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        if (!app.ifInstsComplete()) {
            return true;
        }

        return noDuplicateFindTaclet(app, pos, goal);
    }

    protected boolean comparePio(TacletApp newApp, TacletApp oldApp, PosInOccurrence newPio,
            PosInOccurrence oldPio) {
        return oldPio.equals(newPio);
    }
}
