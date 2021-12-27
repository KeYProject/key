package de.uka.ilkd.key.smt.communication;

import de.uka.ilkd.key.smt.ModelExtractor;
import de.uka.ilkd.key.smt.SMTSolverResult;
import de.uka.ilkd.key.smt.st.SolverType;

import javax.annotation.Nonnull;
import java.io.IOException;

/**
 * The socket for Z3.
 *
 * @author Wolfram Pfeifer (overhaul)
 */
public class Z3Socket extends AbstractSolverSocket {
    /**
     * Creates a new Z3Socket. Should not be called directly, better use the static factory method
     * {@link AbstractSolverSocket#createSocket(SolverType, ModelExtractor)}.
     *
     * @param name  the name of the solver
     * @param query the ModelExtractor for CE generation (unused by this socket)
     */
    public Z3Socket(String name, ModelExtractor query) {
        super(name, query);
    }

}
