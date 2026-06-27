/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Base class for literal values.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * literals: boolean_literal | integer_literal | float_literal | string_literal | char_literal;
 * }</pre>
 */
@NullMarked
public abstract class Literals extends BaseAstNode {
    protected Literals(Position position) {
        super(position);
    }

    @Override
    public abstract <T> T accept(AstVisitor<T> visitor);
}