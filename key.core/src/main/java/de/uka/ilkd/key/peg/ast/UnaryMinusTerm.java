/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents a unary minus term (-term).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * unary_minus_term: MINUS term;
 * }</pre>
 */
@NullMarked
public class UnaryMinusTerm extends BaseAstNode {
    private final Term operand;

    public UnaryMinusTerm(Position position, Term operand) {
        super(position);
        this.operand = operand;
        setChildParent(operand);
    }

    public Term getOperand() {
        return operand;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}