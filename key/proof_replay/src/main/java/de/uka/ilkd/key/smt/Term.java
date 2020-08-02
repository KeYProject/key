package de.uka.ilkd.key.smt;

import java.util.List;

public class Term {
    final Operator op;
    final List<? extends Term> children;

    public Term(Operator op, List<? extends Term> children) {
        this.children = children;
        this.op = op;
    }
}

class Command extends Term {
    public Command(Operator op, List<? extends Term> children) {
        super(op, children);
    }
}
