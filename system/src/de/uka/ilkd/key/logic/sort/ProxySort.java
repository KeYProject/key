package de.uka.ilkd.key.logic.sort;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Name;

public class ProxySort extends AbstractSort {

    public ProxySort(Name name, ImmutableSet<Sort> ext) {
        super(name, ext, false);
    }

    public ProxySort(Name name) {
        this(name, DefaultImmutableSet.<Sort>nil());
    }
}
