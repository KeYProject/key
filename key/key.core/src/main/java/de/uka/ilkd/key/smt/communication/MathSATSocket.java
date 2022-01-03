package de.uka.ilkd.key.smt.communication;

import de.uka.ilkd.key.smt.ModelExtractor;

import javax.annotation.Nonnull;

public class MathSATSocket extends AbstractSolverSocket {

    /**
     * Creates a new solver socket with given solver name and ModelExtractor.
     *
     * @param name  the name of the solver in use
     * @param query the ModelExtractor used to extract a counterexample
     */
    public MathSATSocket(@Nonnull String name, ModelExtractor query) {
        super(name, query);
    }
}
