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
