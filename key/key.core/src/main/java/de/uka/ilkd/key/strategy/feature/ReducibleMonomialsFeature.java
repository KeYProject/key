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
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.metaconstruct.arith.Monomial;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;


/**
 * Return zero iff the monomial <code>dividendSV</code> can be made smaller
 * (in the polynomial reduction ordering) by adding or subtracting
 * <code>divisorSV</code>
 */
public abstract class ReducibleMonomialsFeature extends BinaryTacletAppFeature {
    private final ProjectionToTerm dividend, divisor;

    private ReducibleMonomialsFeature(ProjectionToTerm dividend,
                                      ProjectionToTerm divisor) {
        this.dividend = dividend;
        this.divisor = divisor;
    }

    public static Feature createReducible(ProjectionToTerm dividend,
                                          ProjectionToTerm divisor) {
        return new ReducibleMonomialsFeature ( dividend, divisor ) {
            protected boolean checkReducibility(Monomial mDividend,
                                                Monomial mDivisor) {
                return mDivisor.reducible ( mDividend );
            }            
        };
    }

    public static Feature createDivides(ProjectionToTerm dividend,
                                        ProjectionToTerm divisor) {
        return new ReducibleMonomialsFeature ( dividend, divisor ) {
            protected boolean checkReducibility(Monomial mDividend,
                                                Monomial mDivisor) {
                return mDivisor.divides ( mDividend );
            }            
        };
    }

    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {        
        final Term dividendT = dividend.toTerm ( app, pos, goal );
        final Term divisorT = divisor.toTerm ( app, pos, goal );
        
        final Services services = goal.proof().getServices();
        final Monomial mDividend = Monomial.create ( dividendT, services );
        final Monomial mDivisor = Monomial.create ( divisorT, services );
        
        return checkReducibility ( mDividend, mDivisor );
    }

    protected abstract boolean checkReducibility(Monomial mDividend,
                                                 Monomial mDivisor);
}