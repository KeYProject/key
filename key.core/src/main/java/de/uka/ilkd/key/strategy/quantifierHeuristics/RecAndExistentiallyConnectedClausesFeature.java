/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.java.Services;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Term;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.termfeature.BinaryTermFeature;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;


/**
 * Binary Term Feature return zero if root is a CNF quantifier formula with several clauses. And all
 * the clause are CS-Related.
 */
public class RecAndExistentiallyConnectedClausesFeature extends BinaryTermFeature {
    public static final TermFeature INSTANCE = new RecAndExistentiallyConnectedClausesFeature();

    private RecAndExistentiallyConnectedClausesFeature() {}

    @Override
    protected boolean filter(Term term, MutableState mState, LogicServices services) {
        final ClausesGraph graph = ClausesGraph.create(term, ((Services) services).getCaches());
        return graph.isFullGraph();
    }
}
