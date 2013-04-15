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



package de.uka.ilkd.key.strategy.termProjection;

import java.math.BigInteger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.metaconstruct.arith.Monomial;
import de.uka.ilkd.key.rule.metaconstruct.arith.Polynomial;

/**
 * Given a monomial and a polynomial, this projection computes the gcd of all
 * numerical coefficients. The constant term of the polynomial is ignored. The
 * result is guaranteed to be non-negative.
 */
public class CoeffGcdProjection implements ProjectionToTerm {

    private final ProjectionToTerm monomialLeft;
    private final ProjectionToTerm polynomialRight;
    
    private CoeffGcdProjection(ProjectionToTerm monomialLeft,
                               ProjectionToTerm polynomialRight) {
        this.monomialLeft = monomialLeft;
        this.polynomialRight = polynomialRight;
    }

    public static ProjectionToTerm create(ProjectionToTerm monomialLeft,
                                          ProjectionToTerm polynomialRight) {
        return new CoeffGcdProjection ( monomialLeft, polynomialRight );
    }

    public Term toTerm(RuleApp app, PosInOccurrence pos, Goal goal) {
        final Services services = goal.proof ().getServices ();

        final Term monoT = monomialLeft.toTerm ( app, pos, goal );
        final Term polyT = polynomialRight.toTerm ( app, pos, goal );

        final Monomial mono = Monomial.create ( monoT, services );
        final Polynomial poly = Polynomial.create ( polyT, services );

        final BigInteger gcd = mono.getCoefficient ().gcd ( poly.coeffGcd () );
        return TermBuilder.DF.zTerm ( services, gcd.abs ().toString () );
    }
}
