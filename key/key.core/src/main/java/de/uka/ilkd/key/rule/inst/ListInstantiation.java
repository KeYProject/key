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
