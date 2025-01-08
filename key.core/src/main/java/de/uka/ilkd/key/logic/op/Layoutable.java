package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.util.pp.Layouter;

public interface Layoutable {
    /**
     * Creates a parseable string representation
     *
     * @param l the layouter to use
     */
    void layout(Layouter<?> l);
}
