package de.uka.ilkd.key.rule.inst;

import de.uka.ilkd.key.java.ProgramElement;

/**
 * This class is used to store the instantiation of a schemavarible if it is a ProgramElement.
 */
public class ProgramInstantiation extends InstantiationEntry<ProgramElement> {

    /**
     * creates a new ContextInstantiationEntry
     *
     * @param pe the ProgramElement the SchemaVariable is instantiated with
     */
    ProgramInstantiation(ProgramElement pe) {
        super(pe);
    }
}
