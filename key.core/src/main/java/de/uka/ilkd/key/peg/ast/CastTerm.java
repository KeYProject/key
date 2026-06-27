/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents a cast term ((type)term).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * cast_term: LPAREN sortid RPAREN term;
 * }</pre>
 */
@NullMarked
public class CastTerm extends BaseAstNode {
    private final SortId targetType;
    private final Term operand;

    public CastTerm(Position position, SortId targetType, Term operand) {
        super(position);
        this.targetType = targetType;
        this.operand = operand;
        setChildParent(targetType);
        setChildParent(operand);
    }

    public SortId getTargetType() {
        return targetType;
    }

    public Term getOperand() {
        return operand;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}