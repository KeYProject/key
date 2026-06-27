/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

import java.util.List;

/**
 * Represents one-of sort clause.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * one_of_sorts: LBRACE sortId (COMMA sortId)* RBRACE;
 * }</pre>
 */
@NullMarked
public class OneOfSorts extends BaseAstNode {
    private final List<SortId> sortIds;

    public OneOfSorts(Position position, List<SortId> sortIds) {
        super(position);
        this.sortIds = sortIds;
        for (SortId id : sortIds) {
            setChildParent(id);
        }
    }

    public List<SortId> getSortIds() {
        return sortIds;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}