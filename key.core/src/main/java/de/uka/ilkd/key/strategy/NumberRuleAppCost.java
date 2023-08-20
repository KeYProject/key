/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import javax.annotation.Nonnull;

import de.uka.ilkd.key.util.Debug;

import org.key_project.util.LRUCache;

public abstract class NumberRuleAppCost implements RuleAppCost {

    private static final NumberRuleAppCost ZERO_COST = new IntRuleAppCost(0);
    /**
     * Requires thread save access as multiple proofs may be performed in parallel (Eclipse).
     */
    private static final LRUCache<Integer, NumberRuleAppCost> cache =
        new LRUCache<>(255);

    public static RuleAppCost getZeroCost() {
        return ZERO_COST;
    }

    public static RuleAppCost create(int p_cost) {
        if (p_cost == 0) {
            return NumberRuleAppCost.getZeroCost();
        }

        NumberRuleAppCost ac;
        synchronized (cache) { // Ensure thread save access which is required for parallel proofs
                               // (e.g. in Eclipse)
            ac = cache.get(p_cost);
            if (ac != null) {
                return ac;
            }

            ac = new IntRuleAppCost(p_cost);
            cache.put(p_cost, ac);
        }

        return ac;
    }

    public static RuleAppCost create(long p_cost) {

        if (p_cost <= Integer.MAX_VALUE && p_cost >= Integer.MIN_VALUE) {
            return create((int) p_cost);
        }

        return new LongRuleAppCost(p_cost);
    }

    /**
     * returns the cost
     */
    public abstract long getValue();

    @Nonnull
    @Override
    public RuleAppCost mul(@Nonnull RuleAppCost cost) {
        if (cost instanceof TopRuleAppCost) {
            return cost.mul(this);
        }
        if (cost instanceof NumberRuleAppCost) {
            NumberRuleAppCost numberRuleAppCost = (NumberRuleAppCost) cost;
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



    public boolean equals(Object o) {
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
            Debug.fail("Can't add costs of class " + cost2.getClass());
            // Should not be reached
            return null;
        }
    }

    public final RuleAppCost add(NumberRuleAppCost cost2) {
        if (getValue() == 0) {
            return cost2;
        } else if (cost2.getValue() == 0) {
            return this;
        } else {
            return NumberRuleAppCost.create(getValue() + cost2.getValue());
        }
    }

    @Override
    public String toString() {
        return String.valueOf(getValue());
    }

    /**
     * Implementation of the <code>RuleAppCost</code> interface that uses a <code>long</code> value
     * for the representation of costs, ordered by the usual ordering of natural numbers. Objects of
     * this class are immutable
     */
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
