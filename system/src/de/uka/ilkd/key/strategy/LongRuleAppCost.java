// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.util.Debug;

/**
 * Implementation of the <code>RuleAppCost</code> interface that uses
 * a <code>long</code> value for the representation of costs, ordered by the
 * usual ordering of natural numbers. Objects of this class are immutable
 */
public class LongRuleAppCost implements RuleAppCost {

    public static final LongRuleAppCost ZERO_COST = new LongRuleAppCost ( 0 );

    private final long cost;

    public static RuleAppCost create(long p_cost) {
        if ( p_cost == 0 ) return ZERO_COST;
        return new LongRuleAppCost ( p_cost );
    }
    
    private LongRuleAppCost ( long p_cost ) {
	cost = p_cost;
    }

    public int compareTo(RuleAppCost o) {
	if ( o instanceof TopRuleAppCost )
	    return -1;
	return compareTo((LongRuleAppCost)o);
    }

    public int compareTo(LongRuleAppCost c) {
	return (cost<c.cost ? -1 : (cost==c.cost ? 0 : 1));
    }

    public boolean equals(Object o) {
        if (o instanceof RuleAppCost) { 
            return compareTo ( (RuleAppCost) o ) == 0;
        }
        return false;
    }
    
    public int hashCode() {
        return (int)cost;
    }
    
    public final RuleAppCost add (RuleAppCost cost2) {
        if ( cost2 instanceof LongRuleAppCost ) {
	    return add((LongRuleAppCost) cost2);
	} else if ( cost2 instanceof TopRuleAppCost ) {
            return TopRuleAppCost.INSTANCE;
        } else {
            Debug.fail ( "Can't add costs of class " + cost2.getClass () );
	    // Should not be reached
	    return null;
	}
    }

    public final RuleAppCost add(LongRuleAppCost cost2) {
	if ( cost == 0 ) {
	    return cost2;
	} else if ( cost2.cost == 0 ) {
	    return this;
	} else {
	    return LongRuleAppCost.create ( cost + cost2 .cost );
	}
    }
    
    public long getValue () {
        return cost;
    }
    
    public String toString () {
    	return "Costs " + cost;
    }
}
