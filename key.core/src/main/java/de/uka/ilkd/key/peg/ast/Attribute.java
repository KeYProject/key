/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents an attribute access (object.field).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * attribute: DOT ident;
 * }</pre>
 */
@NullMarked
public class Attribute extends BaseAstNode {
    private final String fieldName;

    public Attribute(Position position, String fieldName) {
        super(position);
        this.fieldName = fieldName;
    }

    public String getFieldName() {
        return fieldName;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}