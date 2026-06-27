/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

import java.util.List;

/**
 * Represents program variable declarations.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * prog_var_decls: PROGRAMVARIABLES LBRACE (keyjavatype var_names SEMI)* RBRACE;
 * }</pre>
 */
@NullMarked
public class ProgVarDecls extends BaseAstNode {
    private final List<KeyJavaType> types;
    private final List<List<String>> varNames;

    public ProgVarDecls(Position position, List<KeyJavaType> types, List<List<String>> varNames) {
        super(position);
        this.types = types;
        this.varNames = varNames;
        for (KeyJavaType t : types) {
            setChildParent(t);
        }
    }

    public List<KeyJavaType> getTypes() {
        return types;
    }

    public List<List<String>> getVarNames() {
        return varNames;
    }
}