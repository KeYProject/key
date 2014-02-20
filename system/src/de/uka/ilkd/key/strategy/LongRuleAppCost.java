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


/**
 * Implementation of the <code>RuleAppCost</code> interface that uses
 * a <code>long</code> value for the representation of costs, ordered by the
 * usual ordering of natural numbers. Objects of this class are immutable
 */
class LongRuleAppCost extends NumberRuleAppCost {

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
