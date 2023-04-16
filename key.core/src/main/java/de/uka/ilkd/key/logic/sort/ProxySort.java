package de.uka.ilkd.key.logic.sort;

import de.uka.ilkd.key.logic.Name;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

public class ProxySort extends AbstractSort {

    public ProxySort(Name name, ImmutableSet<Sort> ext) {
        super(name, ext, false);
    }

    public ProxySort(Name name) {
        this(name, DefaultImmutableSet.nil());
    }
}
