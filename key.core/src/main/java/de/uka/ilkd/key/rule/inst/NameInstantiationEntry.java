package de.uka.ilkd.key.rule.inst;

import de.uka.ilkd.key.logic.Name;

/**
 * This class is used to store the instantiation of a schemavarible if it is a name.
 */
public class NameInstantiationEntry extends InstantiationEntry<Name> {

    NameInstantiationEntry(Name name) {
        super(name);
    }
}
