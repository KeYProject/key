/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents a bracket suffix heap (heap access after bracket).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * bracket_suffix_heap: (LBRACKET term RBRACKET)*;
 * }</pre>
 */
@NullMarked
public class BracketSuffixHeap extends BaseAstNode {
    private final java.util.List<Term> indices;

    public BracketSuffixHeap(Position position, java.util.List<Term> indices) {
        super(position);
        this.indices = indices;
        for (Term t : indices) {
            setChildParent(t);
        }
    }

    public java.util.List<Term> getIndices() {
        return indices;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}