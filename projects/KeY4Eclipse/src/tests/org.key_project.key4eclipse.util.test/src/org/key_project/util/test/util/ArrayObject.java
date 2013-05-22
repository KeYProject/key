/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.util.test.util;

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