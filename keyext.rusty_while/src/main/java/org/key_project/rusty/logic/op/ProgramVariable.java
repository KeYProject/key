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

public class ProgramVariable extends AbstractSortedOperator implements Expr {
    protected ProgramVariable(Name name, Sort s) {
        super(name, s, Modifier.NONE);
    }

    @Override
    public SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException("Program variable does not have a child");
    }

    @Override
    public int getChildCount() {
        return 0;
    }
}
