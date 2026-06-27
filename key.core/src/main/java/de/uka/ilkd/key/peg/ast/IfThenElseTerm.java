/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents an if-then-else term (conditional formula).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * if_then_else_term: IF condition THEN thenBranch ELSE elseBranch END;
 * }</pre>
 */
@NullMarked
public class IfThenElseTerm extends BaseAstNode {
    private final Term condition;
    private final Term thenBranch;
    private final Term elseBranch;

    public IfThenElseTerm(Position position, Term condition, Term thenBranch, Term elseBranch) {
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