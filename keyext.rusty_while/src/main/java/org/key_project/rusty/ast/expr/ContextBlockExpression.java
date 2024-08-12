/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.rusty.ast.stmt.Statement;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.util.collection.ImmutableList;

public class ContextBlockExpression extends BlockExpression {

    public ContextBlockExpression(ImmutableList<? extends Statement> statements, Expr value) {
        super(statements, value);
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnContextBlockExpression(this);
    }
}
