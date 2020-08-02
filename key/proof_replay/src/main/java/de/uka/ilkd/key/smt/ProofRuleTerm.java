package de.uka.ilkd.key.smt;

import java.util.List;

public class ProofRuleTerm extends Term {
    public ProofRuleTerm(Operator op, List<? extends Term> children) {
        super(op, children);
    }
}
