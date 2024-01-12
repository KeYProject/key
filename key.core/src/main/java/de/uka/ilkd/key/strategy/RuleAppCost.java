/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import org.jspecify.annotations.NonNull;

/**
 * Represents the costs of a rule. In the default case this is just an integral number, but in some
 * cases it could be just positive infinity.
 * <p>
 * weigl: It would be better just to implement it on floats!
 */
public interface RuleAppCost extends Comparable<RuleAppCost> {

    int compareTo(@NonNull RuleAppCost o);

    /**
     * Add the given costs to the costs that are represented by this object
     */
    @NonNull
    RuleAppCost add(@NonNull RuleAppCost cost2);


    /**
     * newCost = this * cost.
     *
     * <p>
     * This function is associative. this.mul(a) == a.mul(this)
     * </p>
     *
     * @param cost - non-null {@link RuleAppCost}
     */
    @NonNull
    RuleAppCost mul(@NonNull RuleAppCost cost);
}
