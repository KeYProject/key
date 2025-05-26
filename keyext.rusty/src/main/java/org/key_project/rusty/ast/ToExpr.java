/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast;

import org.key_project.rusty.ast.expr.Expr;

/**
 * An AST element which can be translated to an expression. E.g., a pattern expression
 */
public interface ToExpr {
    Expr toExpr();
}
