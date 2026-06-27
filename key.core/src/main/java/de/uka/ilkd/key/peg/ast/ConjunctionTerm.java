/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents a conjunction term (left && right).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * conjunction_term: left=term AND right=term;
 * }</pre>
 */
@NullMarked
public class ConjunctionTerm extends BaseAstNode {
    private final Term left;
    private final Term right;

    public ConjunctionTerm(Position position, Term left, Term right) {
        super(position);
        this.left = left;
        this.right = right;
        setChildParent(left);
        setChildParent(right);
    }

    public Term getLeft() {
        return left;
    }

    public Term getRight() {
        return right;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}