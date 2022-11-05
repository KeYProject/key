package de.uka.ilkd.key.strategy.termProjection;

import java.math.BigInteger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.LexPathOrdering;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.metaconstruct.arith.Monomial;

public class MonomialColumnOp extends AbstractDividePolynomialsProjection {

    private MonomialColumnOp(ProjectionToTerm leftCoefficient, ProjectionToTerm polynomial) {
        super(leftCoefficient, polynomial);
    }

    public static ProjectionToTerm create(ProjectionToTerm leftCoefficient,
            ProjectionToTerm polynomial) {
        return new MonomialColumnOp(leftCoefficient, polynomial);
    }

    protected Term divide(Monomial numerator, BigInteger denominator, Services services) {
        final BigInteger newRightCoeff =
            LexPathOrdering.divide(numerator.getCoefficient(), denominator);
        return numerator.setCoefficient(newRightCoeff).toTerm(services);
    }
}
