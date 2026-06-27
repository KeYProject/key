/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Represents a bracket term (parenthesized expression).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * bracket_term: LPAREN term RPAREN bracket_suffix_heap?;
 * }</pre>
 */
@NullMarked
public class BracketTerm extends BaseAstNode {
    private final Term inner;
    private final @Nullable BracketSuffixHeap suffix;

    public BracketTerm(Position position, Term inner, @Nullable BracketSuffixHeap suffix) {
        super(position);
        this.inner = inner;
        this.suffix = suffix;
        setChildParent(inner);
        setChildParent(suffix);
    }

    public Term getInner() {
        return inner;
    }

    public @Nullable BracketSuffixHeap getSuffix() {
        return suffix;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}