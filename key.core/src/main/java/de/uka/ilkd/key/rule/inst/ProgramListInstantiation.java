/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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
