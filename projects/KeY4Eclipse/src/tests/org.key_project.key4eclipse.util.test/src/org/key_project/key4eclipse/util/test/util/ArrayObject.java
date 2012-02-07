package org.key_project.key4eclipse.util.test.util;

import org.eclipse.jface.viewers.Viewer;

/**
 * Represents a row object in a {@link Viewer}.
 * @author Martin Hentschel
 */
public class ArrayObject {
    /**
     * The cell values.
     */
    private Object[] values;

    /**
     * Constructor
     * @param values The cell values.
     */
    public ArrayObject(Object... values) {
        super();
        this.values = values;
    }

    /**
     * Returns the cell value at the given index.
     * @param index The index.
     * @return The cell value.
     */
    public Object getValue(int index) {
        if (index >= 0 && index < values.length) {
            return values[index];
        }
        else {
            return null;
        }
    }
    
    /**
     * Counts the number of available values.
     * @return The number of available values.
     */
    public int getValueCount() {
        return values.length;
    }
}
