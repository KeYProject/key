/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.loopinvgen;

import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.io.ProofSaver;

public class LoopInvariantGenerationResult {
    private final Set<Term> conjuncts;
    private final int numberOfLASTIteration;
    private final Services services;

    public LoopInvariantGenerationResult(Set<Term> conjuncts,
            int numberOfLASTIteration, Services services) {
        this.conjuncts = conjuncts;
        this.numberOfLASTIteration = numberOfLASTIteration;
        this.services = services;
    }

    public Set<Term> getConjuncts() {
        return conjuncts;
    }

    public int getNumberOfLASTIterations() {
        return numberOfLASTIteration;
    }

    @Override
    public String toString() {
        StringBuffer result = new StringBuffer("Loop Invariant Generation").append('\n');
        result.append("=========================").append('\n');
        result.append("Number of the LAST Iteration: " + numberOfLASTIteration).append('\n');
        result.append("Conjuncts:\n");
        return result + ProofSaver
                .printTerm(services.getTermBuilder().and(conjuncts), services, true).toString();
    }


    public String conjunctsToString() {
        return ProofSaver.printTerm(services.getTermBuilder().and(conjuncts), services, true)
                .toString();
    }
}
