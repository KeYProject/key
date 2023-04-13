package de.uka.ilkd.key.strategy;

/**
 * Constants and utility functions for dealing with costs encoded as long
 */
public class RuleAppCost {
    public static final long MAX_VALUE = Long.MAX_VALUE;
    public static final long ZERO = 0;

    private RuleAppCost() {}

    /**
     * Adds the sums where any can be {@link RuleAppCost.MAX_VALUE}.
     *
     * @param left any cost
     * @param right any cost
     * @return the sum
     */
    public static long add(long left, long right) {
        if (left == MAX_VALUE || right == MAX_VALUE)
            return MAX_VALUE;
        return left + right;
    }

    /**
     * Adds the sums where right must not be {@link RuleAppCost.MAX_VALUE}.
     *
     * @param left any cost
     * @param right cost != {@link RuleAppCost.MAX_VALUE}.
     * @return the sum
     */
    public static long addRight(long left, long right) {
        if (left == MAX_VALUE)
            return MAX_VALUE;
        return left + right;
    }
}
