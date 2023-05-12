package de.uka.ilkd.key.proof.io.intermediate;

import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.util.Pair;

public class SMTAppIntermediate extends BuiltInAppIntermediate {
    private final String solver;

    public SMTAppIntermediate(String ruleName, Pair<Integer, PosInTerm> pos, String solver) {
        super(ruleName, pos, null, null, null);
        this.solver = solver;
    }

    public String getSolver() {
        return solver;
    }
}
