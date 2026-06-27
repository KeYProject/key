/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

import java.util.List;

/**
 * Represents schema variable declarations.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * schema_var_decls: SCHEMAVARIABLES LBRACE (one_schema_var_decl SEMI)* RBRACE;
 * }</pre>
 */
@NullMarked
public class SchemaVarDecls extends BaseAstNode {
    private final List<OneSchemaVarDecl> decls;

    public SchemaVarDecls(Position position, List<OneSchemaVarDecl> decls) {
        super(position);
        this.decls = decls;
        for (OneSchemaVarDecl d : decls) {
            setChildParent(d);
        }
    }

    public List<OneSchemaVarDecl> getDecls() {
        return decls;
    }
}
