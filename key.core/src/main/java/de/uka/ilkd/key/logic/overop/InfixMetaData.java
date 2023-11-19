/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.overop;

import java.util.stream.Collectors;

import de.uka.ilkd.key.logic.op.Function;

import org.key_project.util.collection.ImmutableArray;

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
