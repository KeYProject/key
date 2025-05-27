/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.hir.expr;

import org.key_project.rusty.parser.hir.Span;
import org.key_project.rusty.parser.hir.hirty.HirTy;
import org.key_project.rusty.parser.hir.pat.Pat;

import org.jspecify.annotations.Nullable;

public record LetExpr(Span span, Pat pat, @Nullable HirTy ty, Expr init, boolean recovered) {
}
