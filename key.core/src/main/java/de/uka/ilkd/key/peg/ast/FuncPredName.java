/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Represents a function/predicate name with optional sort prefix.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * funcpred_name: (sortId DOUBLECOLON)? (name=simple_ident_dots|num=INT_LITERAL);
 * }</pre>
 */
@NullMarked
public class FuncPredName extends BaseAstNode {
    private final @Nullable SortId sortPrefix;
    private final @Nullable SimpleIdentDots name;
    private final @Nullable String intLiteral;

    public FuncPredName(Position position, @Nullable SortId sortPrefix, SimpleIdentDots name) {
        super(position);
        this.sortPrefix = sortPrefix;
        this.name = name;
        this.intLiteral = null;
        if (sortPrefix != null) setChildParent(sortPrefix);
        setChildParent(name);
    }

    public FuncPredName(Position position, @Nullable SortId sortPrefix, String intLiteral) {
        super(position);
        this.sortPrefix = sortPrefix;
        this.name = null;
        this.intLiteral = intLiteral;
        if (sortPrefix != null) setChildParent(sortPrefix);
    }

    public @Nullable SortId getSortPrefix() {
        return sortPrefix;
    }

    public @Nullable SimpleIdentDots getName() {
        return name;
    }

    public @Nullable String getIntLiteral() {
        return intLiteral;
    }
}