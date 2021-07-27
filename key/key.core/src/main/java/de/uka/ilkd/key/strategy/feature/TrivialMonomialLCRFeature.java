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
 * Return zero of the least common reducible of two monomials is so trivial that
 * it is not necessary to do the critical pair completion
 * 
 * "A critical-pair/completion algorithm for finitely generated ideals in rings"
 */
public class TrivialMonomialLCRFeature extends BinaryTacletAppFeature {
    private final ProjectionToTerm a, b;

    private TrivialMonomialLCRFeature(ProjectionToTerm a, ProjectionToTerm b) {
        this.a = a;
        this.b = b;
    }

    public static Feature create(ProjectionToTerm a, ProjectionToTerm b) {
        return new TrivialMonomialLCRFeature ( a, b );
    }

    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        final Services services = goal.proof().getServices();
        final Monomial aMon =
            Monomial.create ( a.toTerm ( app, pos, goal ), services );
        final Monomial bMon =
            Monomial.create ( b.toTerm ( app, pos, goal ), services );
        
/*        final BigInteger ac = aMon.getCoefficient ();
        final BigInteger bc = bMon.getCoefficient ();
        
        if ( ac.mod ( bc ).signum () != 0 && bc.mod ( ac ).signum () != 0 )
            return false; */
            
        return aMon.variablesAreCoprime ( bMon );
   }
}