package de.uka.ilkd.key.logic.overop;

import de.uka.ilkd.key.logic.op.Function;
import org.key_project.util.collection.ImmutableArray;

import java.util.stream.Collectors;

public class InfixMetaData implements FunctionMetaData {
    private final ImmutableArray<String> infixOperator;
    private final int prec;

    public InfixMetaData(ImmutableArray<String> names, int prec) {
        this.infixOperator = names;
        this.prec = prec;
    }

    public InfixMetaData(String text, int prec) {
        this(new ImmutableArray<>(text), prec);
    }

    @Override
    public int getPrecedence() {
        return prec;
    }

    @Override
    public boolean isInfix() {
        return true;
    }

    @Override
    public Iterable<String> getAlternativeSignatures(Function fun) {
        var sig = fun.argSorts().stream().map(it -> it.name().toString())
                .collect(Collectors.joining(",", "(", ")"));
        return infixOperator.stream().map(it -> it + sig)
                .collect(Collectors.toList());
    }
}
