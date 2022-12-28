package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.sort.Sort;

public interface Sorted {
    /**
     * the sort of the entity
     *
     * @return the {@link Sort} of the sorted entity
     */
    Sort sort();
}
