/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.rusty.Services;
import org.key_project.rusty.logic.op.ProgramFunction;
import org.key_project.util.collection.ImmutableArray;

public interface Call extends Expr {
    Expr callee();

    ImmutableArray<Expr> params();

    ProgramFunction function(Services services);
}
