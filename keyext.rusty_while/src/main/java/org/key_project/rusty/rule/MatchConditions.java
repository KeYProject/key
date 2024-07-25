package org.key_project.rusty.rule;

import org.key_project.rusty.rule.inst.SVInstantiations;

public class MatchConditions {
    private final SVInstantiations instantiations;

    public MatchConditions() {
        this.instantiations = SVInstantiations.EMPTY_SVINSTANTIATIONS;
    }

    public MatchConditions(SVInstantiations p_instantiations) {
        assert p_instantiations != null;
        instantiations = p_instantiations;
    }

    public SVInstantiations getInstantiations() {
        return instantiations;
    }

    public MatchConditions setInstantiations(SVInstantiations p_instantiations) {
        if (instantiations == p_instantiations) {
            return this;
        } else {
            return new MatchConditions(p_instantiations);
        }
    }
}
