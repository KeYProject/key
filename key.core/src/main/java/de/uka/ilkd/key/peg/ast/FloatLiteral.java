/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents a float literal.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * float_literal: FLOAT_LITERAL;
 * }</pre>
 */
@NullMarked
public class FloatLiteral extends Literals {
    private final String value;

    public FloatLiteral(Position position, String value) {
        super(position);
        this.value = value;
    }

    public String getValue() {
        return value;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}