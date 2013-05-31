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


package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.LongRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;

/**
 * Abstract superclass for features that have either zero cost or top cost.
 */
public abstract class BinaryTermFeature implements TermFeature {

    protected BinaryTermFeature () {}
    
    /** Constant that represents the boolean value true */
    public static final RuleAppCost ZERO_COST = LongRuleAppCost.ZERO_COST;
    /** Constant that represents the boolean value false */
    public static final RuleAppCost TOP_COST  = TopRuleAppCost.INSTANCE;
    
    final public RuleAppCost compute ( Term term ) {
        return filter ( term ) ? ZERO_COST : TOP_COST; 
    }
    
    protected abstract boolean filter ( Term term );

}
