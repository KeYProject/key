/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Base interface for single sort declarations.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * one_sort_decl: doc=DOC_COMMENT? (GENERIC ... | PROXY ... | ABSTRACT? ... | ALIAS ...);
 * }</pre>
 */
@NullMarked
public interface OneSortDecl extends AstNode {
    @Nullable String getDocComment();
}