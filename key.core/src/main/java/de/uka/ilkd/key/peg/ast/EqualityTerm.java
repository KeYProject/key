/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents an equality term (left == right or left != right).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * equality_term: left=term (EQUALS | NOT_EQUALS) right=term;
 * }</pre>
 */
@NullMarked
public class EqualityTerm extends BaseAstNode {
    private final Term left;
    private final Term right;
    private final boolean isEquality;

    public EqualityTerm(Position position, Term left, Term right, boolean isEquality) {
        super(position);
        this.left = left;
        this.right = right;
        this.isEquality = isEquality;
        setChildParent(left);
        setChildParent(right);
    }

    public Term getLeft() {
        return left;
    }

    public Term getRight() {
        return right;
    }

    public boolean isEquality() {
        return isEquality;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}