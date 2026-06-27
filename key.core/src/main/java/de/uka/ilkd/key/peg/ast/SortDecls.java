/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

import java.util.List;

/**
 * Represents sort declarations.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * sort_decls: SORTS LBRACE (one_sort_decl)* RBRACE;
 * }</pre>
 */
@NullMarked
public class SortDecls extends BaseAstNode {
    private final List<OneSortDecl> sortDecls;

    public SortDecls(Position position, List<OneSortDecl> sortDecls) {
        super(position);
        this.sortDecls = sortDecls;
        for (OneSortDecl decl : sortDecls) {
            setChildParent(decl);
        }
    }

    public List<OneSortDecl> getSortDecls() {
        return sortDecls;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}