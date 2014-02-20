package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.util.Debug;

public abstract class NumberRuleAppCost implements RuleAppCost {

    private static final IntRuleAppCost ZERO_COST = new IntRuleAppCost ( 0 );

    public static RuleAppCost getZeroCost() {
        return ZERO_COST;
    }
    
    public static RuleAppCost create(int p_cost) {
        
        if ( p_cost == 0 ) return NumberRuleAppCost.getZeroCost();
        
        return new IntRuleAppCost ( p_cost );
    }
    
    public static RuleAppCost create(long p_cost) {
        
        if ( p_cost == 0 ) return NumberRuleAppCost.getZeroCost();
        
        if ( p_cost <= Integer.MAX_VALUE && p_cost >= Integer.MIN_VALUE) {
            return new IntRuleAppCost((int)p_cost);
        }        
        
        return new LongRuleAppCost ( p_cost );
    }
    
    /**
     * returns the cost
     */
    public abstract long getValue();


    @Override
    public int compareTo(RuleAppCost o) {
        if ( o instanceof TopRuleAppCost )
            return -1;
        return compareTo((NumberRuleAppCost)o);
    }
    
    
    public int compareTo(NumberRuleAppCost c) {
        final long this_cost = getValue();
        final long other_cost = c.getValue(); 
        return (this_cost<other_cost ? -1 : (this_cost==other_cost ? 0 : 1));
    }

    
    
    public boolean equals(Object o) {
        if (o instanceof RuleAppCost) { 
            return compareTo ( (RuleAppCost) o ) == 0;
        }
        return false;
    }
    
    public int hashCode() {
        return (int)getValue();
    }
    
    public final RuleAppCost add (RuleAppCost cost2) {
        if ( cost2 instanceof NumberRuleAppCost ) {
            return add((NumberRuleAppCost) cost2);
        } else if ( cost2 instanceof TopRuleAppCost ) {
            return TopRuleAppCost.INSTANCE;
        } else {
            Debug.fail ( "Can't add costs of class " + cost2.getClass () );
            // Should not be reached
            return null;
        }
    }

    public final RuleAppCost add(NumberRuleAppCost cost2) {
        if ( getValue() == 0 ) {
            return cost2;
        } else if ( cost2.getValue() == 0 ) {
            return this;
        } else {
            return NumberRuleAppCost.create ( getValue() + cost2 .getValue() );
        }
    }

}
