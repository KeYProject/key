package de.uka.ilkd.key.smt;

import java.util.ArrayList;

public class Symbol extends Term {
    private final String name;

    public Symbol(String name) {
        super(Operator.SYMBOL, new ArrayList<>());
        this.name = name;
    }

    @Override
    public String toString() {
        return name;
    }
}
