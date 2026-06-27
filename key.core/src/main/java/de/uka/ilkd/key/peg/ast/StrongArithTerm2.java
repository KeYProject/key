/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents a strong arithmetic term with two operands (*, /, %).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * strong_arith_term2: left=term (MULT | DIV | MOD) right=term;
 * }</pre>
 */
@NullMarked
public class StrongArithTerm2 extends BaseAstNode {
    public enum Op { MUL, DIV, MOD }
    
    private final Term left;
    private final Term right;
    private final Op operator;

    public StrongArithTerm2(Position position, Term left, Term right, Op operator) {
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