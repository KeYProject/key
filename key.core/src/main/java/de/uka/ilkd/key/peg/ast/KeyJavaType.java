/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents a KeY Java type.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * key_java_type: ident_dots;
 * }</pre>
 */
@NullMarked
public class KeyJavaType extends BaseAstNode {
    private final String typeName;

    public KeyJavaType(Position position, String typeName) {
        super(position);
        this.typeName = typeName;
    }

    public String getTypeName() {
        return typeName;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}