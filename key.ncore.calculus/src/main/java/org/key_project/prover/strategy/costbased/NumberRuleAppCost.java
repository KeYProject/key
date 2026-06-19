/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public abstract class NumberRuleAppCost implements RuleAppCost {

    private static final NumberRuleAppCost ZERO_COST = new IntRuleAppCost(0);

    /// Pre-allocated instances for frequently occurring cost values.
    /// The array is filled once during class initialization and
    /// only read afterwards, so access needs no synchronization. This method is critical as
    /// it is called for every feature evaluation.
    private static final int CACHE_LOW = -8192;
    private static final int CACHE_HIGH = 8192;
    private static final IntRuleAppCost[] CACHE = new IntRuleAppCost[CACHE_HIGH - CACHE_LOW];

    static {
        for (int i = 0; i < CACHE.length; i++) {
            CACHE[i] = new IntRuleAppCost(CACHE_LOW + i);
        }
    }

    public static RuleAppCost getZeroCost() {
        return ZERO_COST;
    }

    public static RuleAppCost create(int p_cost) {
        if (p_cost == 0) {
            return getZeroCost();
        }
        if (p_cost >= CACHE_LOW && p_cost < CACHE_HIGH) {
            return CACHE[p_cost - CACHE_LOW];
        }
        return new IntRuleAppCost(p_cost);
    }

    public static RuleAppCost create(long p_cost) {

        if (p_cost <= Integer.MAX_VALUE && p_cost >= Integer.MIN_VALUE) {
            return create((int) p_cost);
        }

        return new LongRuleAppCost(p_cost);
    }

    /// returns the cost
    public abstract long getValue();

    @Override
    public @NonNull RuleAppCost mul(@NonNull RuleAppCost cost) {
        if (cost instanceof TopRuleAppCost) {
            return cost.mul(this);
        }
        if (cost instanceof NumberRuleAppCost numberRuleAppCost) {
            return create(getValue() * numberRuleAppCost.getValue());
        }
        throw new IllegalArgumentException();
    }

    @Override
    public int compareTo(RuleAppCost o) {
        if (o instanceof TopRuleAppCost) {
            return -1;
        }
        return compareTo((NumberRuleAppCost) o);
    }


    public int compareTo(NumberRuleAppCost c) {
        final long this_cost = getValue();
        final long other_cost = c.getValue();
        return (Long.compare(this_cost, other_cost));
    }



    public boolean equals(@Nullable Object o) {
        if (o instanceof RuleAppCost) {
            return compareTo((RuleAppCost) o) == 0;
        }
        return false;
    }

    public int hashCode() {
        return (int) getValue();
    }

    public final RuleAppCost add(RuleAppCost cost2) {
        if (cost2 instanceof NumberRuleAppCost) {
            return add((NumberRuleAppCost) cost2);
        } else if (cost2 instanceof TopRuleAppCost) {
            return TopRuleAppCost.INSTANCE;
        } else {
            throw new AssertionError("Can't add costs of class " + cost2.getClass());
        }
    }

    public final RuleAppCost add(NumberRuleAppCost cost2) {
        if (getValue() == 0) {
            return cost2;
        } else if (cost2.getValue() == 0) {
            return this;
        } else {
            return create(getValue() + cost2.getValue());
        }
    }

    @Override
    public String toString() {
        return String.valueOf(getValue());
    }

    /// Implementation of the <code>RuleAppCost</code> interface that uses a <code>long</code> value
    /// for the representation of costs, ordered by the usual ordering of natural numbers. Objects
    /// of
    /// this class are immutable
    private final static class LongRuleAppCost extends NumberRuleAppCost {

        private final long cost;

        private LongRuleAppCost(long p_cost) {
            cost = p_cost;
        }

        @Override
        public long getValue() {
            return cost;
        }
    }


    private final static class IntRuleAppCost extends NumberRuleAppCost {

        private final int cost;

        private IntRuleAppCost(int p_cost) {
            this.cost = p_cost;
        }


        @Override
        public long getValue() {
            return cost;
        }
    }

}
