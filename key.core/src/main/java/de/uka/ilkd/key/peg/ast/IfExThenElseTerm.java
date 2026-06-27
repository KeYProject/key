/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents an if-ex-then-else term (conditional expression with ? :).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * if_ex_then_else_term: condition QUESTION thenBranch COLON elseBranch;
 * }</pre>
 */
@NullMarked
public class IfExThenElseTerm extends BaseAstNode {
    private final Term condition;
    private final Term thenBranch;
    private final Term elseBranch;

    public IfExThenElseTerm(Position position, Term condition, Term thenBranch, Term elseBranch) {
        super(position);
        this.condition = condition;
        this.thenBranch = thenBranch;
        this.elseBranch = elseBranch;
        setChildParent(condition);
        setChildParent(thenBranch);
        setChildParent(elseBranch);
    }

    public Term getCondition() {
        return condition;
    }

    public Term getThenBranch() {
        return thenBranch;
    }

    public Term getElseBranch() {
        return elseBranch;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}