/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import javax.annotation.Nonnull;

/**
 * Singleton implementation of the <code>RuleAppCost</code> interface, which denotes a maximum cost
 * (rule applications with this cost can't be afforded at all)
 */
public class TopRuleAppCost implements RuleAppCost {

    private TopRuleAppCost() {}

    public int compareTo(@Nonnull RuleAppCost o) {
        if (o instanceof TopRuleAppCost) {
            return 0;
        }
        return 1;
    }

    public boolean equals(Object o) {
        if (o instanceof RuleAppCost) {
            return compareTo((RuleAppCost) o) == 0;
        }
        return false;
    }

    public int hashCode() {
        return 91879827;
    }

    /**
     * TOP costs cannot be further increased!
     *
     * @param cost2 the other costs
     * @return this instance
     */
    public final RuleAppCost add(@Nonnull RuleAppCost cost2) {
        return INSTANCE;
    }

    /**
     * Multiply the TOP costs with given cost. TOP times any other costs results into TOP cost.
     *
     * (weigl: Dicussable whether {@code TOP times 0 = 0}?)
     *
     * @param cost - non-null {@link RuleAppCost}
     * @return this instance
     */
    @Nonnull
    @Override
    public RuleAppCost mul(@Nonnull RuleAppCost cost) {
        return this;
    }

    public String toString() {
        return "Costs infinite";
    }

    public static final TopRuleAppCost INSTANCE = new TopRuleAppCost();

}
