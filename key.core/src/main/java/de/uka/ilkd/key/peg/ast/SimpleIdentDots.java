/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents a simple identifier with dots (qualified name).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * simple_ident_dots: ident+=simple_ident (DOT ident+=simple_ident)*;
 * }</pre>
 */
@NullMarked
public class SimpleIdentDots extends BaseAstNode {
    private final String fullName;

    public SimpleIdentDots(Position position, String fullName) {
        super(position);
        this.fullName = fullName;
    }

    public String getFullName() {
        return fullName;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}