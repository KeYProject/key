/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.annotation;

import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.visitor.Visitor;

/**
 * This is the abstract class representing a Java annotation (like @Override 
 * or @NonNull). 
 *
 * @author Daniel Grévent
 */
public abstract class Annotation extends JavaNonTerminalProgramElement {
    protected final KeYJavaType type;

    public Annotation(KeYJavaType type) {
        this.type = type;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnAnnotation(this);
    }

    public KeYJavaType getKeyJavaType() {
        return type;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }

        return o instanceof Annotation annot
                ? annot.type.equals(type) && super.equals(o)
                : false;
    }
}
