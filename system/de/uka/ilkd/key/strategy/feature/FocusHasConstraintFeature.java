package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

public class FocusHasConstraintFeature extends BinaryFeature {

    public final static Feature INSTANCE = new FocusHasConstraintFeature ();
    
    private FocusHasConstraintFeature () {}
    
    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
        assert pos != null : "Feature is only applicable to rules with find";
        return !pos.constrainedFormula ().constraint ().isBottom ();
    }
}
