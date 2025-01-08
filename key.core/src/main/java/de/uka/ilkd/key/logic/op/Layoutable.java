package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.util.pp.Layouter;

/**
 * Current workaround to factor out layout method from SchemaVariable
 * This inteface should be removed and the knowledge how to print a parseable
 * representation of a variable declaration moved out of the logic package. The reason
 * is that logic elements should not be responsible to know how their concrete syntax
 * looks like.
 */
public interface Layoutable {
    /**
     * Creates a parseable string representation
     *
     * @param l the layouter to use
     */
    void layout(Layouter<?> l);
}
