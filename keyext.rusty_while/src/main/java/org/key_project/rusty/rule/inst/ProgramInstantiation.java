/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.inst;

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
