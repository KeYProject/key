/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.op;

import org.key_project.logic.Name;
import org.key_project.logic.op.Modifier;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.ast.expr.Expr;
import org.key_project.rusty.ast.ty.KeYRustyType;

public abstract class ProgramVariable extends AbstractSortedOperator implements Expr {
    private final KeYRustyType type;

    protected ProgramVariable(Name name, Sort s, KeYRustyType t,
            KeYRustyType containingType) {
        super(name, s == null ? t.getSort() : s, Modifier.NONE);
        this.type = t;
    }
}
