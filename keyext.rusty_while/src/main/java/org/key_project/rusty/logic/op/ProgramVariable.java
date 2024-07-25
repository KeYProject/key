/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.op;

import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.AbstractSortedOperator;
import org.key_project.logic.op.Modifier;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.ast.expr.Expr;
import org.key_project.rusty.ast.ty.KeYRustyType;

import org.jspecify.annotations.NonNull;

public class ProgramVariable extends AbstractSortedOperator implements Expr {
    private final KeYRustyType type;

    public ProgramVariable(Name name, Sort s, KeYRustyType type) {
        super(name, s, Modifier.NONE);
        this.type = type;
    }

    public ProgramVariable(Name name, KeYRustyType type) {
        this(name, type.getSort(), type);
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException("Program variable does not have a child");
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    public KeYRustyType getKeYRustyType() {
        return type;
    }
}
