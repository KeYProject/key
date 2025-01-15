/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.instantiation;


public abstract class MatchConditions {
    protected final SVInstantiations instantiations;

    protected MatchConditions(SVInstantiations p_instantiations) {
        assert p_instantiations != null;
        instantiations = p_instantiations;
    }

    public SVInstantiations getInstantiations() {
        return instantiations;
    }

    public abstract MatchConditions setInstantiations(SVInstantiations p_instantiations);
}
