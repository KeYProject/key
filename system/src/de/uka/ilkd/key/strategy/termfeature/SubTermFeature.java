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
 * Feature for invoking a list of term features on the direct subterms of a
 * given term. The result will be the sum of the individual results. If the
 * arity of the term investigated does not coincide with the number of term
 * features that are given as arguments, <code>arityMismatchCost</code> will
 * be returned
 */
public class SubTermFeature implements TermFeature {

    private SubTermFeature(TermFeature[] features, RuleAppCost arityMismatchCost) {
        this.features = features;
        this.arityMismatchCost = arityMismatchCost;
    }
    
    public static TermFeature create (TermFeature[] fs, RuleAppCost arityMismatchCost) {
        final TermFeature[] fsCopy = new TermFeature [ fs.length ];
        System.arraycopy ( fs, 0, fsCopy, 0, fs.length );
        return new SubTermFeature ( fsCopy, arityMismatchCost );
    }

    public static TermFeature create(TermFeature[] fs) {
        return create ( fs, TopRuleAppCost.INSTANCE );
    }
    
    private final TermFeature[] features;
    private final RuleAppCost arityMismatchCost;
    
    public RuleAppCost compute(Term term) {
        if ( term.arity () != features.length ) return arityMismatchCost;
        
        RuleAppCost res = LongRuleAppCost.ZERO_COST;

        for ( int i = 0; i < features.length
                         && !( res instanceof TopRuleAppCost ); i++ )
            res = res.add ( features[i].compute ( term.sub(i) ) );

        return res;
    }
}
