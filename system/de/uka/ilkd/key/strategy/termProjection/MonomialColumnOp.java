// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.strategy.termProjection;

import java.math.BigInteger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.LexPathOrdering;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.metaconstruct.arith.Monomial;

public class MonomialColumnOp extends AbstractDividePolynomialsProjection {

    private MonomialColumnOp(ProjectionToTerm leftCoefficient,
                             ProjectionToTerm polynomial) {
        super ( leftCoefficient, polynomial );
    }

    public static ProjectionToTerm create(ProjectionToTerm leftCoefficient,
                                          ProjectionToTerm polynomial) {
        return new MonomialColumnOp ( leftCoefficient, polynomial );
    }

    protected Term divide(Monomial numerator, BigInteger denominator,
                          Services services) {
        final BigInteger newRightCoeff =
            LexPathOrdering.divide ( numerator.getCoefficient (), denominator );
        return numerator.setCoefficient ( newRightCoeff ).toTerm ( services );
    }
}
