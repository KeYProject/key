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

package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.metaconstruct.arith.Monomial;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;

/**
 * Feature that decides whether the multiplication of two inequations (using
 * rules of set inEqSimp_nonLin_multiply) is allowed. We only do this if the
 * product of the left sides of the inequations has factors in common with the
 * left side of some other inequation, similarly to how it is decided in the
 * Buchberger algorithm.
 */
public abstract class InEquationMultFeature extends BinaryTacletAppFeature {

    protected final ProjectionToTerm targetCandidate;
    protected final ProjectionToTerm mult1Candidate;
    protected final ProjectionToTerm mult2Candidate;
    
    /**
     * Return zero iff the multiplication of mult1 and mult2 is allowed,
     * because the resulting product is partially covered by target.
     *
     * @param mult1Candidate
     *            the left side of the first inequation to be multiplied
     * @param mult2Candidate
     *            the left side of the second inequation to be multiplied
     * @param targetCandidate
     *            the left side of the inequation that is supposed to bound the
     *            other two inequations
     */
    public static Feature partiallyBounded(ProjectionToTerm mult1Candidate,
                                           ProjectionToTerm mult2Candidate,
                                           ProjectionToTerm targetCandidate) {
        return new InEquationMultFeature ( mult1Candidate,
                                           mult2Candidate,
                                           targetCandidate ) {
            protected boolean filter(Monomial targetM, Monomial mult1M, Monomial mult2M) {
                return !mult2M.reduce ( targetM ).variablesDisjoint ( mult1M )
                       && !mult1M.reduce ( targetM ).variablesDisjoint ( mult2M );
            }            
        };
    }

    /**
     * Return zero iff the product of mult1 and mult2 is a factor of target
     */
    public static Feature totallyBounded(ProjectionToTerm mult1Candidate,
                                         ProjectionToTerm mult2Candidate,
                                         ProjectionToTerm targetCandidate) {
        return new InEquationMultFeature ( mult1Candidate,
                                           mult2Candidate,
                                           targetCandidate ) {
            protected boolean filter(Monomial targetM, Monomial mult1M, Monomial mult2M) {
                return targetM.variablesSubsume ( mult1M.multiply ( mult2M ) );
            }            
        };
    }

    /**
     * Return zero iff the product of mult1 and mult2 is target
     */
    public static Feature exactlyBounded(ProjectionToTerm mult1Candidate,
                                         ProjectionToTerm mult2Candidate,
                                         ProjectionToTerm targetCandidate) {
        return new InEquationMultFeature ( mult1Candidate,
                                           mult2Candidate,
                                           targetCandidate ) {
            protected boolean filter(Monomial targetM, Monomial mult1M, Monomial mult2M) {
                return targetM.variablesEqual ( mult1M.multiply ( mult2M ) );
            }            
        };
    }

    protected InEquationMultFeature(ProjectionToTerm mult1Candidate,
                                     ProjectionToTerm mult2Candidate,
                                     ProjectionToTerm targetCandidate) {
        this.mult1Candidate = mult1Candidate;
        this.mult2Candidate = mult2Candidate;
        this.targetCandidate = targetCandidate;
    }

    protected final boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        final Services services = goal.proof ().getServices ();
        final Monomial targetM =
            Monomial.create ( targetCandidate.toTerm ( app, pos, goal ),
                              services );
        final Monomial mult1M =
            Monomial.create ( mult1Candidate.toTerm ( app, pos, goal ),
                              services );                
        final Monomial mult2M =
            Monomial.create ( mult2Candidate.toTerm ( app, pos, goal ),
                              services );
        
        return filter ( targetM, mult1M, mult2M );
    }

    protected abstract boolean filter(Monomial targetM,
                                      Monomial mult1M,
                                      Monomial mult2M);
}