// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.strategy;

import javax.annotation.Nonnull;

/**
 * Represents the costs of a rule. In the default case this is just an integral number,
 * but in some cases it could be just positive infinity.
 * <p>
 * weigl: It would be better just to implement it on floats!
 */
public interface RuleAppCost extends Comparable<RuleAppCost> {

    int compareTo(@Nonnull RuleAppCost o);

    /**
     * Add the given costs to the costs that are represented by this object
     */
    @Nonnull
    RuleAppCost add(@Nonnull RuleAppCost cost2);


    /**
     * newCost = this * cost.
     *
     * <p>This function is associative. this.mul(a) == a.mul(this)</p>
     *
     * @param cost - non-null {@link RuleAppCost}
     */
    @Nonnull
    RuleAppCost mul(@Nonnull RuleAppCost cost);
}