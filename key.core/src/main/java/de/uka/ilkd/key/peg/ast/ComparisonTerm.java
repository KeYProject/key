/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents a comparison term (left <,>,=<,>= right).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * comparison_term: left=term (LT | GT | LE | GE) right=term;
 * }</pre>
 */
@NullMarked
public class ComparisonTerm extends BaseAstNode {
    public enum Op { LT, GT, LE, GE }
    
    private final Term left;
    private final Term right;
    private final Op operator;

    public ComparisonTerm(Position position, Term left, Term right, Op operator) {
        super(position);
        this.left = left;
        this.right = right;
        this.operator = operator;
        setChildParent(left);
        setChildParent(right);
    }

    public Term getLeft() {
        return left;
    }

    public Term getRight() {
        return right;
    }

    public Op getOperator() {
        return operator;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}