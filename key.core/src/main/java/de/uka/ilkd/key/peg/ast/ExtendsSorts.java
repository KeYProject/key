/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

import java.util.List;

/**
 * Represents extends sort clause.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * extends_sorts: sortId (COMMA sortId)*;
 * }</pre>
 */
@NullMarked
public class ExtendsSorts extends BaseAstNode {
    private final List<SortId> sortIds;

    public ExtendsSorts(Position position, List<SortId> sortIds) {
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