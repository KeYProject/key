package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

public class FocusInAntecFeature extends BinaryFeature {

    private FocusInAntecFeature() {}

    public static final Feature INSTANCE = new FocusInAntecFeature();

    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
        assert pos != null : "Feature is only applicable to rules with find";
        return pos.isInAntec();
    }
}
