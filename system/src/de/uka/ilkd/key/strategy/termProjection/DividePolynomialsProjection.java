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
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.metaconstruct.arith.Monomial;

public abstract class DividePolynomialsProjection
                                  extends AbstractDividePolynomialsProjection {

    private DividePolynomialsProjection(ProjectionToTerm leftCoefficient,
                                      ProjectionToTerm polynomial) {
        super ( leftCoefficient, polynomial );
    }

    public static ProjectionToTerm createRoundingDown(ProjectionToTerm leftCoefficient,
                                                      ProjectionToTerm polynomial) {
        return new DividePolynomialsProjection ( leftCoefficient, polynomial ) {
            protected Term divide(Monomial numerator, BigInteger denominator,
                                  Services services) {
                final BigInteger newRightCoeff =
                    divide ( numerator.getCoefficient (), denominator );
                return numerator.setCoefficient ( newRightCoeff ).toTerm ( services );
            }

        };
    }

    public static ProjectionToTerm createRoundingUp(ProjectionToTerm leftCoefficient,
                                                    ProjectionToTerm polynomial) {
        return new DividePolynomialsProjection ( leftCoefficient, polynomial ) {
            protected Term divide(Monomial numerator, BigInteger denominator,
                                  Services services) {
                final BigInteger newRightCoeff =
                    divide ( numerator.getCoefficient ().negate (), denominator ).negate ();
                return numerator.setCoefficient ( newRightCoeff ).toTerm ( services );
            }            
        };
    }

    protected BigInteger divide(BigInteger numerator, BigInteger denominator) {
        final BigInteger remainder = numerator.remainder(denominator);
        
        BigInteger res = numerator.divide ( denominator );
        if ( remainder.signum () != 0 && numerator.signum () < 0 ) {
            if ( denominator.signum () > 0 )
                res = res.subtract ( BigInteger.ONE );
            else
                res = res.add ( BigInteger.ONE );
        }
        return res;
    }            
}
