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

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.termfeature.BinaryTermFeature;
import de.uka.ilkd.key.strategy.termfeature.TermFeature;


/**
 * Binary Term Feature return zero if root is a CNF quantifier formula with several 
 * clauses. And all the clause are CS-Related.
 */
public class RecAndExistentiallyConnectedClausesFeature extends BinaryTermFeature {
    public static final TermFeature INSTANCE =
        new RecAndExistentiallyConnectedClausesFeature ();

    private RecAndExistentiallyConnectedClausesFeature() {}

    protected boolean filter(Term term) {
        final ClausesGraph graph = ClausesGraph.create ( term );
        return graph.isFullGraph ();
    }
}
