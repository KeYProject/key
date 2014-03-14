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


package de.uka.ilkd.key.strategy.feature;

import java.util.Iterator;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;
import de.uka.ilkd.key.strategy.termProjection.TermBuffer;
import de.uka.ilkd.key.strategy.termgenerator.TermGenerator;

/**
 * A feature that computes the sum of the values of a feature term when a given
 * variable ranges over a sequence of terms
 */
public class ComprehendedSumFeature implements Feature {
    
    private final TermBuffer var;
    private final TermGenerator generator;
    private final Feature body;

    /**
     * @param var
     *            <code>TermBuffer</code> in which the terms are going to
     *            be stored
     * @param generator
     *            the terms that are to be iterated over
     * @param body
     *            a feature that is supposed to be evaluated repeatedly for the
     *            possible values of <code>var</code>
     */
    public static Feature create(TermBuffer var,
                                 TermGenerator generator,
                                 Feature body) {
        return new ComprehendedSumFeature ( var, generator, body );
    }

    private ComprehendedSumFeature(TermBuffer var,
                                   TermGenerator generator,
                                   Feature body) {
        this.var = var;
        this.generator = generator;
        this.body = body;
    }

    
    public RuleAppCost compute (RuleApp app, PosInOccurrence pos, Goal goal) {        
        final Term outerVarContent = var.getContent ();
        
        final Iterator<Term> it = generator.generate ( app, pos, goal );
        RuleAppCost res = NumberRuleAppCost.getZeroCost();
        while ( it.hasNext () && ! ( res instanceof TopRuleAppCost ) ) {
            var.setContent ( it.next () );
            
            res = res.add ( body.compute ( app, pos, goal ) );
        }
        
        var.setContent ( outerVarContent );
        return res;
    }
}
