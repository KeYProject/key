/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents a schema variable declaration.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * schema_var_decl: kind IDENT;
 * }</pre>
 */
@NullMarked
public class SchemaVarDecl extends BaseAstNode {
    private final String name;
    private final String kind;

    public SchemaVarDecl(Position position, String name, String kind) {
        super(position);
        this.name = name;
        this.kind = kind;
    }

    public String getName() {
        return name;
    }

    public String getKind() {
        return kind;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}