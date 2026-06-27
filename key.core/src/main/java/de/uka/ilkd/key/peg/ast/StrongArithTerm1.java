/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents a strong arithmetic term with one operand (*, /, %).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * strong_arith_term1: (MULT | DIV | MOD) term;
 * }</pre>
 */
@NullMarked
public class StrongArithTerm1 extends BaseAstNode {
    public enum Op { MUL, DIV, MOD }
    
    private final Term operand;
    private final Op operator;

    public StrongArithTerm1(Position position, Term operand, Op operator) {
        super(position);
        this.operand = operand;
        this.operator = operator;
        setChildParent(operand);
    }

    public Term getOperand() {
        return operand;
    }

    public Op getOperator() {
        return operator;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}