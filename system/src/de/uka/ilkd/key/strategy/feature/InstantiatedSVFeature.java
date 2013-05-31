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



package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;
import de.uka.ilkd.key.strategy.termProjection.SVInstantiationProjection;

/**
 * Feature that returns zero iff a certain schema variable is instantiated (or
 * does not occur in the taclet at hand)
 */
public class InstantiatedSVFeature extends BinaryTacletAppFeature {

    private final ProjectionToTerm instProj;

    public static Feature create(Name svName) {
        return new InstantiatedSVFeature ( svName );
    }

    private InstantiatedSVFeature(Name svName) {
        instProj = SVInstantiationProjection.create ( svName, false );
    }

    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        return instProj.toTerm ( app, pos, goal ) != null;
    }

}
