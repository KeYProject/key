/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast;

import de.uka.ilkd.key.java.visitor.Visitor;

public abstract class Annotation extends JavaNonTerminalProgramElement {
    protected final String name;

    public Annotation(String name) {
        this.name = name;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnAnnotation(this);
    }

    public String getName() {
        return name;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;
        return ((Annotation) o).name.equals(name) && super.equals(o);
    }
}
