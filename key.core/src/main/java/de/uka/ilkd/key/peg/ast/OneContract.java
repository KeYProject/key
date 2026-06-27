/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents a single contract definition.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * one_contract: ident COLON term NEWLINE modifiable_clause?;
 * }</pre>
 */
@NullMarked
public class OneContract extends BaseAstNode {
    private final String name;
    private final Term formula;
    private final Term modifiableClause;

    public OneContract(Position position, String name, Term formula, Term modifiableClause) {
        super(position);
        this.name = name;
        this.formula = formula;
        this.modifiableClause = modifiableClause;
        setChildParent(formula);
        setChildParent(modifiableClause);
    }

    public String getName() {
        return name;
    }

    public Term getFormula() {
        return formula;
    }

    public Term getModifiableClause() {
        return modifiableClause;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}