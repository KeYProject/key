package de.uka.ilkd.key.logic.sort;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.logic.Name;

/**
 * Standard implementation of the Sort interface.
 */
public final class SortImpl extends AbstractSort {

    public SortImpl(Name name, ImmutableSet<Sort> ext, boolean isAbstract) {
        super(name, ext, isAbstract);
    }

    public SortImpl(Name name, ImmutableSet<Sort> ext) {
        this(name, ext, false);
    }

    public SortImpl(Name name, Sort ext) {
        this(name, DefaultImmutableSet.<Sort>nil().add(ext), false);
    }


    public SortImpl(Name name) {
        this(name, DefaultImmutableSet.<Sort>nil());
    }

    public boolean equals(Object o) {
        if (o instanceof SortImpl) {
            return ((SortImpl) o).name().equals(name());
        } else
            return false;
    }

}
