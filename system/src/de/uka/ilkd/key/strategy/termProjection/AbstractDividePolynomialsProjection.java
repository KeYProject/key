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
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.metaconstruct.arith.Monomial;

public abstract class AbstractDividePolynomialsProjection implements ProjectionToTerm {

    private final ProjectionToTerm leftCoefficient, polynomial;
    
    protected AbstractDividePolynomialsProjection(ProjectionToTerm leftCoefficient,
                                          ProjectionToTerm polynomial) {
        this.leftCoefficient = leftCoefficient;
        this.polynomial = polynomial;
    }

    public Term toTerm(RuleApp app, PosInOccurrence pos, Goal goal) {
        final Term coeffT = leftCoefficient.toTerm ( app, pos, goal );
        final Term polyT = polynomial.toTerm ( app, pos, goal );

        final Services services = goal.proof ().getServices ();
        final BigInteger coeff =
            new BigInteger ( AbstractTermTransformer
                             .convertToDecimalString ( coeffT, services ) );

        return quotient ( coeff, polyT, services );
    }

    protected abstract Term divide(Monomial numerator, BigInteger denominator,
                                   Services services);

    private Term quotient(BigInteger monoCoeff, Term rightPoly, Services services) {
        final Function add = 
            services.getTypeConverter ().getIntegerLDT ().getAdd ();
        if ( rightPoly.op () == add ) {
            final Term left = quotient ( monoCoeff, rightPoly.sub ( 0 ),
                                         services );
            final Term right = quotient ( monoCoeff, rightPoly.sub ( 1 ),
                                          services );
            return TermBuilder.DF.func ( add, left, right );
        }
        
        final Monomial rightMono = Monomial.create ( rightPoly, services );
        return divide ( rightMono, monoCoeff, services );
    }

}
