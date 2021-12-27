package de.uka.ilkd.key.smt.communication;

import de.uka.ilkd.key.smt.ModelExtractor;
import de.uka.ilkd.key.smt.SMTSolverResult;

import javax.annotation.Nonnull;
import java.io.IOException;

public class PrincessSocket extends AbstractSolverSocket {

    public PrincessSocket(String name, ModelExtractor query) {
        super(name, query);
    }

}
