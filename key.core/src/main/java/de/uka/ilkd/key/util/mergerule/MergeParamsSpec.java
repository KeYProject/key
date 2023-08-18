/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.mergerule;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.speclang.MergeContract;

import org.key_project.util.collection.ImmutableList;

/**
 * Specification of merge parameters for the creation of {@link MergeContract}s;
 *
 *
 * @author Dominic Scheurer
 */
public class MergeParamsSpec {
    private final String latticeType;
    private final LocationVariable placeholder;
    private final ImmutableList<Term> predicates;

    public MergeParamsSpec(String latticeType, LocationVariable placeholder,
            ImmutableList<Term> predicates) {
        this.latticeType = latticeType;
        this.placeholder = placeholder;
        this.predicates = predicates;
    }

    public String getLatticeType() {
        return latticeType;
    }

    public LocationVariable getPlaceholder() {
        return placeholder;
    }

    public ImmutableList<Term> getPredicates() {
        return predicates;
    }
}
