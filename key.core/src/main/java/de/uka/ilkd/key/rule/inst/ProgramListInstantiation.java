package de.uka.ilkd.key.rule.inst;

import de.uka.ilkd.key.java.ProgramElement;

import org.key_project.util.collection.ImmutableArray;

/**
 * This class is used to store the instantiation of a schemavariable if it is a ProgramElement.
 */

public class ProgramListInstantiation extends InstantiationEntry<ImmutableArray<ProgramElement>> {

    /**
     * creates a new ContextInstantiationEntry
     *
     * @param pes the ProgramElement array the SchemaVariable is instantiated with
     */
    ProgramListInstantiation(ImmutableArray<ProgramElement> pes) {
        super(pes);
    }
}
