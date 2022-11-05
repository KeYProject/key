package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;


/**
 * Term has the post condition term label.
 */
public final class IsPostConditionTermFeature extends BinaryTermFeature {

    public static final IsPostConditionTermFeature INSTANCE = new IsPostConditionTermFeature();


    private IsPostConditionTermFeature() {
    }


    @Override
    protected boolean filter(Term t, Services services) {
        return t.hasLabels() && t.containsLabel(ParameterlessTermLabel.POST_CONDITION_LABEL);
    }
}
