package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.logic.Term;

import java.util.Set;

public class LoopInvariantGenerationResult {
    private final Set<Term> conjuncts;
    private final int numberOfLASTIteration;

    public LoopInvariantGenerationResult(Set<Term> conjuncts,
                                         int numberOfLASTIteration) {
        this.conjuncts = conjuncts;
        this.numberOfLASTIteration = numberOfLASTIteration;
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
        for (Term term : conjuncts) {
            result.append(term).append('\n');
            System.out.println(term);
        }
        return result.toString();
    }
}
