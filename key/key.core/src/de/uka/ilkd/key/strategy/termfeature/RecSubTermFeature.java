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

package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;


/**
 * Feature for invoking a term feature recursively on all subterms of a term.
 * The result will be the sum of the individual results for subterms. The
 * feature descends to subterms as long as <code>cond</code> returns zero.
 */
public class RecSubTermFeature implements TermFeature {
    
    private final TermFeature cond, summand;

    private RecSubTermFeature(TermFeature cond, TermFeature summand) {
        this.cond = cond;
        this.summand = summand;
    }
    
    public static TermFeature create(TermFeature cond, TermFeature summand) {
        return new RecSubTermFeature ( cond, summand );
    }

    public RuleAppCost compute(Term term, Services services) {
        RuleAppCost res = summand.compute(term, services);

        if ( res instanceof TopRuleAppCost ||
             cond.compute ( term, services ) instanceof TopRuleAppCost ) return res;
        
        for ( int i = 0; i != term.arity ()
                         && !( res instanceof TopRuleAppCost ); ++i )
            res = res.add ( compute ( term.sub ( i ), services ) );

        return res;
    }
}