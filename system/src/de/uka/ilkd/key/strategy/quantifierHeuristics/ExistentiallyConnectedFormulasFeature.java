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



package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.feature.BinaryTacletAppFeature;
import de.uka.ilkd.key.strategy.feature.Feature;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;

/**
 * Binary feature that return zero if two given projection term is CS-Releated.
 */
public class ExistentiallyConnectedFormulasFeature extends
        BinaryTacletAppFeature {

    private final ProjectionToTerm for0, for1;

    private ExistentiallyConnectedFormulasFeature(ProjectionToTerm for0,
                                                  ProjectionToTerm for1) {
        this.for0 = for0;
        this.for1 = for1;
    }

    public static Feature create(ProjectionToTerm for0, ProjectionToTerm for1) {
        return new ExistentiallyConnectedFormulasFeature ( for0, for1 );
    }

    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        assert pos != null : "Feature is only applicable to rules with find";

        final ClausesGraph graph =
            ClausesGraph.create ( pos.constrainedFormula ().formula () );

        return graph.connected ( for0.toTerm ( app, pos, goal ),
                                 for1.toTerm ( app, pos, goal ) );
    }

}
    
    
