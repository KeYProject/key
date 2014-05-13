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

import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.LRUCache;

public abstract class NumberRuleAppCost implements RuleAppCost {

    private static final NumberRuleAppCost ZERO_COST = new IntRuleAppCost ( 0 );
    private static final LRUCache<Integer,NumberRuleAppCost> cache = new LRUCache<Integer,NumberRuleAppCost>(255);

    public static RuleAppCost getZeroCost() {
        return ZERO_COST;
    }
    
    public static RuleAppCost create(int p_cost) {
        
        if ( p_cost == 0 ) return NumberRuleAppCost.getZeroCost();
        
        NumberRuleAppCost ac = cache.get(p_cost);
        if (ac != null) return ac;
        
        ac = new IntRuleAppCost(p_cost);
        cache.put(p_cost, ac);

        return ac;
    }
    
    public static RuleAppCost create(long p_cost) {
        
        if ( p_cost <= Integer.MAX_VALUE && p_cost >= Integer.MIN_VALUE) {
            return create ((int) p_cost);
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


    /**
     * Implementation of the <code>RuleAppCost</code> interface that uses
     * a <code>long</code> value for the representation of costs, ordered by the
     * usual ordering of natural numbers. Objects of this class are immutable
     */
    private final static class LongRuleAppCost extends NumberRuleAppCost {

        private final long cost;

        protected LongRuleAppCost ( long p_cost ) {
            cost = p_cost;
        }

        @Override
        public final long getValue () {
            return cost;
        }
        
        public String toString () {
            return "Costs " + cost;
        }
    }


    private final static class IntRuleAppCost extends NumberRuleAppCost {

        private final int cost;

        protected IntRuleAppCost(int p_cost) {
            this.cost = p_cost;
        }

     
        @Override
        public
        final long getValue() {
            return cost;
        }
    }

}