package org.key_project.rusty.rule.inst;

import org.key_project.logic.Term;
import org.key_project.rusty.ast.RustyProgramElement;

/**
 * This class is used to store the instantiation of a schemavarible if it is a ProgramElement.
 */
public class ProgramInstantiation extends InstantiationEntry<RustyProgramElement> {

    /**
     * creates a new ContextInstantiationEntry
     *
     * @param pe the ProgramElement the SchemaVariable is instantiated with
     */
    ProgramInstantiation(RustyProgramElement pe) {
        super(pe);
    }
}