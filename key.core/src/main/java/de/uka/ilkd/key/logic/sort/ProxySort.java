package de.uka.ilkd.key.logic.sort;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.logic.Name;

public class ProxySort extends AbstractSort {

    public ProxySort(Name name, ImmutableSet<Sort> ext) {
        super(name, ext, false);
    }

    public ProxySort(Name name) {
        this(name, DefaultImmutableSet.<Sort>nil());
    }
}
