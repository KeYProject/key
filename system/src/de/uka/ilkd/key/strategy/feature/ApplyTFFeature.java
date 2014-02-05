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

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;
import de.uka.ilkd.key.strategy.termfeature.TermFeature;
import de.uka.ilkd.key.util.Debug;

/**
 * Feature for invoking a term feature on the instantiation of a schema variable
 */
public class ApplyTFFeature implements Feature {

    private final ProjectionToTerm proj;
    private final TermFeature      termFeature;
    private final RuleAppCost      noInstCost;
    private final boolean          demandInst;

    /**
     * @param proj
     *            the ProjectionToTerm to the instantiation is supposed to be
     *            inspected
     * @param termFeature
     *            the term feature to use
     * @param noInstCost
     *            result if <code>schemaVar</code> is not instantiated
     * @param demandInst
     *            if <code>true</code> then raise an exception if
     *            <code>schemaVar</code> is not instantiated (otherwise:
     *            return <code>noInstCost</code>)
     */
    private ApplyTFFeature(ProjectionToTerm proj,
                           TermFeature termFeature,
                           RuleAppCost noInstCost,
                           boolean demandInst) {
        this.proj = proj;
        this.termFeature = termFeature;
        this.noInstCost = noInstCost;
        this.demandInst = demandInst;
    }

    public static Feature createNonStrict(ProjectionToTerm proj, TermFeature tf,
                                          RuleAppCost noInstCost) {
        return new ApplyTFFeature ( proj, tf, noInstCost, false );
    }

    public static Feature create(ProjectionToTerm proj, TermFeature tf) {
        return new ApplyTFFeature ( proj, tf, TopRuleAppCost.INSTANCE, true );
    }

    public RuleAppCost compute(RuleApp app, PosInOccurrence pos, Goal goal) {
        final Term te = proj.toTerm ( app, pos, goal );
        if ( te == null ) {
            Debug.assertFalse ( demandInst,
                                "ApplyTFFeature: got undefined argument (null)" );
            return noInstCost;
        }

        return termFeature.compute ( te, goal.proof().getServices() );
    }

}
