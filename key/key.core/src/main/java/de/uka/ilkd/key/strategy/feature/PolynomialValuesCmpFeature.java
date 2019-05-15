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

import java.math.BigInteger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.metaconstruct.arith.Polynomial;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;

/**
 * Return zero only if the value of one (left) polynomial always will be (less
 * or equal) or (less) than the value of a second (right) polynomial.
 * Both polynomials can optionally be multiplied with some constant before
 * comparison.
 */
public abstract class PolynomialValuesCmpFeature extends BinaryTacletAppFeature {

    private final ProjectionToTerm left, right, leftCoeff, rightCoeff;
    
    protected PolynomialValuesCmpFeature(ProjectionToTerm left,
                                         ProjectionToTerm right,
                                         ProjectionToTerm leftCoeff,
                                         ProjectionToTerm rightCoeff) {
        this.left = left;
        this.right = right;
        this.leftCoeff = leftCoeff;
        this.rightCoeff = rightCoeff;
    }

    public static Feature lt(ProjectionToTerm left, ProjectionToTerm right) {
        return lt ( left, right, null, null );
    }
    
    public static Feature lt(ProjectionToTerm left,
                             ProjectionToTerm right,
                             ProjectionToTerm leftCoeff,
                             ProjectionToTerm rightCoeff) {
        return new PolynomialValuesCmpFeature ( left,
                                                right,
                                                leftCoeff,
                                                rightCoeff ) {
            protected boolean compare(Polynomial leftPoly, Polynomial rightPoly) {
                return leftPoly.valueLess ( rightPoly );                
            }
        };
    }
    
    public static Feature leq(ProjectionToTerm left, ProjectionToTerm right) {
        return leq ( left, right, null, null );
    }
    
    public static Feature leq(ProjectionToTerm left,
                              ProjectionToTerm right,
                              ProjectionToTerm leftCoeff,
                              ProjectionToTerm rightCoeff) {
        return new PolynomialValuesCmpFeature ( left,
                                                right,
                                                leftCoeff,
                                                rightCoeff ) {
            protected boolean compare(Polynomial leftPoly, Polynomial rightPoly) {
                return leftPoly.valueLeq ( rightPoly );
            }
        };
    }
    
    public static Feature eq(ProjectionToTerm left, ProjectionToTerm right) {
        return eq ( left, right, null, null );
    }
    
    public static Feature eq(ProjectionToTerm left,
                             ProjectionToTerm right,
                             ProjectionToTerm leftCoeff,
                             ProjectionToTerm rightCoeff) {
        return new PolynomialValuesCmpFeature ( left,
                                                right,
                                                leftCoeff,
                                                rightCoeff ) {
            protected boolean compare(Polynomial leftPoly, Polynomial rightPoly) {
                return leftPoly.valueEq ( rightPoly );
            }
        };
    }
    
    public static Feature divides(ProjectionToTerm left, ProjectionToTerm right) {
        return divides ( left, right, null, null );
    }
    
    public static Feature divides(ProjectionToTerm left,
                                  ProjectionToTerm right,
                                  ProjectionToTerm leftCoeff,
                                  ProjectionToTerm rightCoeff) {
        return new PolynomialValuesCmpFeature ( left,
                                                right,
                                                leftCoeff,
                                                rightCoeff ) {
            protected boolean compare(Polynomial leftPoly, Polynomial rightPoly) {
                // we currently only support constant polynomials
                assert leftPoly.getParts ().isEmpty ();
                assert rightPoly.getParts ().isEmpty ();
                if ( leftPoly.getConstantTerm ().signum() == 0 ) return true;
                if ( rightPoly.getConstantTerm ().signum() == 0 ) return false;
                return
                    leftPoly.getConstantTerm ()
                    .mod ( rightPoly.getConstantTerm ().abs () ).signum () == 0;
            }
        };
    }
    
    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        return compare ( getPolynomial ( left, leftCoeff, app, pos, goal ),
                         getPolynomial ( right, rightCoeff, app, pos, goal ) );
    }

    protected abstract boolean compare(Polynomial leftPoly, Polynomial rightPoly);
    
    private Polynomial getPolynomial(ProjectionToTerm polyProj,
                                     ProjectionToTerm coeffProj,
                                     TacletApp app,
                                     PosInOccurrence pos,
                                     Goal goal) {
        final Services services = goal.proof ().getServices ();
        final Polynomial poly =
            Polynomial.create ( polyProj.toTerm ( app, pos, goal ), services );

        if (coeffProj == null) return poly;
        final Term coeffT = coeffProj.toTerm ( app, pos, goal );
        if ( coeffT == null ) return poly;
        
        final BigInteger coeff =
            new BigInteger ( AbstractTermTransformer
                             .convertToDecimalString ( coeffT, services ) );
        return poly.multiply ( coeff );
    }
}