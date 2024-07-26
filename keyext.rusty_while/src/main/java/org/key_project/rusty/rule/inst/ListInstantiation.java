/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.inst;

import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.util.collection.ImmutableList;

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
