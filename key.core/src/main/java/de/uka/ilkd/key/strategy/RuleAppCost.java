package de.uka.ilkd.key.strategy;

/**
 *
 */
public interface RuleAppCost extends Comparable<RuleAppCost> {

    public int compareTo (RuleAppCost o);

    /**
     * Add the given costs to the costs that are represented by this object
     */
    RuleAppCost add (RuleAppCost cost2);

}