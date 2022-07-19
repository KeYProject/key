package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.logic.Term;

import java.util.Set;

class LoopInvariantGenerationResult {
    private final Set<Term> conjuncts;
    private final int numberOfIterations;

    public LoopInvariantGenerationResult(Set<Term> conjuncts,
                                         int numberOfIterations) {
        this.conjuncts = conjuncts;
        this.numberOfIterations = numberOfIterations;
    }

    public Set<Term> getConjuncts() {
        return conjuncts;
    }

    public int getNumberOfIterations() {
        return numberOfIterations;
    }

    @Override
    public String toString() {
        StringBuffer result = new StringBuffer("Loop Invariant Generation").append('\n');
        result.append("=========================").append('\n');
        result.append("Number of Iterations: " + numberOfIterations).append('\n');
        result.append("Conjuncts:\n");
        for (Term term : conjuncts) {
            result.append(term).append('\n');
            System.out.println(term);
        }
        return result.toString();
    }
}
