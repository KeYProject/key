/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents a method/function call.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * call: LPAREN (term (COMMA term)*)? RPAREN;
 * }</pre>
 */
@NullMarked
public class Call extends BaseAstNode {
    private final java.util.List<Term> arguments;

    public Call(Position position, java.util.List<Term> arguments) {
        super(position);
        this.arguments = arguments;
        for (Term t : arguments) {
            setChildParent(t);
        }
    }

    public java.util.List<Term> getArguments() {
        return arguments;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}