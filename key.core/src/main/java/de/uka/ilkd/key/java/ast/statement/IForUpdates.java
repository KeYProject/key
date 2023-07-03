package de.uka.ilkd.key.java.ast.statement;

import de.uka.ilkd.key.java.ast.Expression;
import de.uka.ilkd.key.java.ast.TerminalProgramElement;

import org.key_project.util.collection.ImmutableArray;

public interface IForUpdates extends TerminalProgramElement {

    int size();

    Expression getExpressionAt(int i);

    ImmutableArray<Expression> getUpdates();

}
