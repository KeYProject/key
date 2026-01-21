package de.uka.ilkd.key.java;


/**
 * Named program element. taken from COMPOST and changed to achieve an immutable structure
 */

public interface NamedProgramElement extends NamedModelElement, NonTerminalProgramElement {

    /**
     * Get identifier.
     *
     * @return the identifier.
     */
    de.uka.ilkd.key.logic.ProgramElementName getProgramElementName();

}
