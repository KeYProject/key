/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.instantiation;

/**
 * Container class used to track the current rule matching status
 */
public abstract class MatchResultInfo {
    protected final SVInstantiations instantiations;

    protected MatchResultInfo(SVInstantiations p_instantiations) {
        assert p_instantiations != null;
        instantiations = p_instantiations;
    }

    public SVInstantiations getInstantiations() {
        return instantiations;
    }

    public abstract MatchResultInfo setInstantiations(SVInstantiations p_instantiations);
}
