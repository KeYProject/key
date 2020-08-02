package de.uka.ilkd.key.smt;

public class Operator {
    private final String name;
    private final int arity;

    public static final Operator SYMBOL = new Operator("symbol", 0);

    public Operator(String name, int arity) {
        this.name = name;
        this.arity = arity;
    }
}

class ProofRule extends Operator {
    public ProofRule(String name, int arity) {
        super(name, arity);
    }
}

class Function extends Operator {
    public Function(String name, int arity) {
        super(name, arity);
    }
}

class Quantifier extends Operator {
    public static final Operator FORALL = new Quantifier("forall", 2);
    public static final Operator EXISTS = new Quantifier("exists", 2);

    public Quantifier(String name, int arity) {
        super(name, arity);
    }
}
