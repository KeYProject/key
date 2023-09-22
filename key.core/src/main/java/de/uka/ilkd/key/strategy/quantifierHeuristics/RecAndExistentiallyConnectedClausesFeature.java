/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.termfeature.BinaryTermFeature;
import de.uka.ilkd.key.strategy.termfeature.TermFeature;


/**
 * Binary Term Feature return zero if root is a CNF quantifier formula with several clauses. And all
 * the clause are CS-Related.
 */
public class RecAndExistentiallyConnectedClausesFeature extends BinaryTermFeature {
    public static final TermFeature INSTANCE = new RecAndExistentiallyConnectedClausesFeature();

    private RecAndExistentiallyConnectedClausesFeature() {}

    protected boolean filter(Term term, Services services) {
        final ClausesGraph graph = ClausesGraph.create(term, services.getCaches());
        return graph.isFullGraph();
    }
}
