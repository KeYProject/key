/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.inst;

import org.key_project.prover.rules.instantiation.InstantiationEntry;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.util.collection.ImmutableArray;

/**
 * This class is used to store the instantiation of a schemavariable if it is a ProgramElement.
 */

public class ProgramListInstantiation
        extends InstantiationEntry<ImmutableArray<RustyProgramElement>> {

    /**
     * creates a new ContextInstantiationEntry
     *
     * @param pes the ProgramElement array the SchemaVariable is instantiated with
     */
    ProgramListInstantiation(ImmutableArray<RustyProgramElement> pes) {
        super(pes);
    }
}
