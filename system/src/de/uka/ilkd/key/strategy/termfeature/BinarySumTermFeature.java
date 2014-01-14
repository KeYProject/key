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

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;

/**
 * A feature that computes the sum of two given features (faster than the more
 * general class <code>SumFeature</code>)
 */
public class BinarySumTermFeature implements TermFeature {

    public RuleAppCost compute(Term term, Services services) {
        RuleAppCost f0Cost = f0.compute ( term, services );
        if ( f0Cost instanceof TopRuleAppCost ) return f0Cost;
        return f0Cost.add ( f1.compute ( term, services ) );
    }

    private BinarySumTermFeature(TermFeature f0, TermFeature f1) {
        this.f0 = f0;
        this.f1 = f1;
    }

    public static TermFeature createSum(TermFeature f0, TermFeature f1) {
        return new BinarySumTermFeature ( f0, f1 );
    }

    private final TermFeature f0, f1;
}
