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