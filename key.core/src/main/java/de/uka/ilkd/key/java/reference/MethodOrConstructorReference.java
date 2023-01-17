package de.uka.ilkd.key.java.reference;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Statement;

public interface MethodOrConstructorReference extends MemberReference, ReferencePrefix, Statement {

    /**
     * @return the array wrapper of the argument expressions .
     */
    ImmutableArray<? extends Expression> getArguments();
}
