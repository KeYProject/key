/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast.annotation;

import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;

/**
 * This corresponds to a Java {@link Annotation} without arguments,
 * like @Override or @NonNull.
 *
 * @author Daniel Grévent
 */
public class MarkerAnnotation extends Annotation {
    public MarkerAnnotation(KeYJavaType type) {
        super(type);
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        throw new ArrayIndexOutOfBoundsException();
    }

    @Override
    public String toString() {
        return "@" + type.getJavaType().toString();
    }
}
