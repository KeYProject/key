package de.uka.ilkd.key.java.statement;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.Expression;

public interface IForUpdates extends de.uka.ilkd.key.java.TerminalProgramElement {

    int size();

    Expression getExpressionAt(int i);

    ImmutableArray<Expression> getUpdates();

}
