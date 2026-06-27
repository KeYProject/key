/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents a quantifier term (forall/exists).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * quantifier_term: (FORALL | EXISTS) bound_variables DOT term;
 * }</pre>
 */
@NullMarked
public class QuantifierTerm extends BaseAstNode {
    private final boolean isUniversal;
    private final BoundVariables variables;
    private final Term body;

    public QuantifierTerm(Position position, boolean isUniversal, BoundVariables variables, Term body) {
        super(position);
        this.isUniversal = isUniversal;
        this.variables = variables;
        this.body = body;
        setChildParent(variables);
        setChildParent(body);
    }

    public boolean isUniversal() {
        return isUniversal;
    }

    public BoundVariables getVariables() {
        return variables;
    }

    public Term getBody() {
        return body;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}