// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.util.mergerule;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.speclang.MergeContract;
import de.uka.ilkd.key.speclang.jml.translation.KeYJMLParser;

/**
 * Specification of merge parameters for the creation of {@link MergeContract}s;
 * this is used by {@link KeYJMLParser}.
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
