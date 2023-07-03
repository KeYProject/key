package de.uka.ilkd.key.java.ast.reference;

import de.uka.ilkd.key.java.ast.Expression;
import de.uka.ilkd.key.java.ast.Statement;

import org.key_project.util.collection.ImmutableArray;

public interface MethodOrConstructorReference extends MemberReference, ReferencePrefix, Statement {

    /**
     * @return the array wrapper of the argument expressions .
     */
    ImmutableArray<? extends Expression> getArguments();
}
