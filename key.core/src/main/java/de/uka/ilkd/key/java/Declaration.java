package de.uka.ilkd.key.java;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.declaration.Modifier;


/**
 * Declaration. taken from COMPOST and changed to achieve an immutable structure
 */
public interface Declaration extends NonTerminalProgramElement {

    /**
     * Get the modifiers.
     *
     * @return the (original) list of modifiers wrapped .
     */
    ImmutableArray<Modifier> getModifiers();
}
