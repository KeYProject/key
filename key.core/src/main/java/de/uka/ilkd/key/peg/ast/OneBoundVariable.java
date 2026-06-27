/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Represents a single bound variable.
 * Corresponds to: s=sortId? id=simple_ident;
 *
 * @author Cline
 * @version 1.0
 */
@NullMarked
public class OneBoundVariable extends BaseAstNode {
    private final @Nullable SortId sort;
    private final String name;

    public OneBoundVariable(Position position, @Nullable SortId sort, String name) {
        super(position);
        this.sort = sort;
        this.name = name;
        setChildParent(sort);
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    public @Nullable SortId getSort() {
        return sort;
    }

    public String getName() {
        return name;
    }
}