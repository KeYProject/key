/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents a boolean literal (true/false).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * boolean_literal: TRUE | FALSE;
 * }</pre>
 */
@NullMarked
public class BooleanLiteral extends Literals {
    private final boolean value;

    public BooleanLiteral(Position position, boolean value) {
        super(position);
        this.value = value;
    }

    public boolean getValue() {
        return value;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}