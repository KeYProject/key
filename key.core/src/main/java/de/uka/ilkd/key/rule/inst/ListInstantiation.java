/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.rule.inst;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.op.SchemaVariable;

public class ListInstantiation extends InstantiationEntry<ImmutableList<Object>> {

    /**
     * creates a new ContextInstantiationEntry
     *
     * @param sv the SchemaVariable that is instantiated
     * @param pes the List the SchemaVariable is instantiated with
     */
    ListInstantiation(SchemaVariable sv, ImmutableList<Object> pes) {
        super(pes);
    }
}
