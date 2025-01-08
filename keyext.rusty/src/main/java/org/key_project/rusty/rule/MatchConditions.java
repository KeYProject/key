/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import org.key_project.rusty.rule.inst.SVInstantiations;

public class MatchConditions extends org.key_project.prover.rules.MatchConditions {
    public static final MatchConditions EMPTY_MATCHCONDITIONS =
        new MatchConditions(SVInstantiations.EMPTY_SVINSTANTIATIONS);

    public MatchConditions() {
        super(SVInstantiations.EMPTY_SVINSTANTIATIONS);
    }

    public MatchConditions(SVInstantiations p_instantiations) {
        super(p_instantiations);
    }

    public SVInstantiations getInstantiations() {
        return (SVInstantiations) instantiations;
    }

    public MatchConditions setInstantiations(
            org.key_project.prover.rules.inst.SVInstantiations p_instantiations) {
        if (instantiations == p_instantiations) {
            return this;
        } else {
            return new MatchConditions((SVInstantiations) p_instantiations);
        }
    }
}
