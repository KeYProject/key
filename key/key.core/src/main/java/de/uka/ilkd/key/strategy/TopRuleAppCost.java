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
 * Singleton implementation of the <code>RuleAppCost</code> interface, which
 * denotes a maximum cost (rule applications with this cost can't be afforded
 * at all)
 */
public class TopRuleAppCost implements RuleAppCost {

    private TopRuleAppCost () {}

    public int compareTo(@Nonnull RuleAppCost o) {
	if ( o instanceof TopRuleAppCost )
	    return 0;
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
     * @param cost2 the other costs
     * @return this instance
     */
    public final RuleAppCost add(@Nonnull RuleAppCost cost2) {
        return INSTANCE;
    }

    /**
     * Multiply the TOP costs with given cost.
     * TOP times any other costs results into TOP cost.
     *
     * (weigl: Dicussable whether {@code TOP times 0 = 0}?)
     * @param cost - non-null {@link RuleAppCost}
     * @return this instance
     */
    @Nonnull
    @Override
    public RuleAppCost mul(@Nonnull RuleAppCost cost) {
        return this;
    }

    public String toString () {
        return "Costs infinite";
    }

    public static final TopRuleAppCost INSTANCE = new TopRuleAppCost ();

}