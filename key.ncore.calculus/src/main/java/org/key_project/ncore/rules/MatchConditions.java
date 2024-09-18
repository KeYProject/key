/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.ncore.rules;


import org.key_project.ncore.rules.inst.SVInstantiations;

public class MatchConditions {
    public static final MatchConditions EMPTY_MATCHCONDITIONS =
        new MatchConditions(SVInstantiations.EMPTY_SVINSTANTIATIONS);

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
