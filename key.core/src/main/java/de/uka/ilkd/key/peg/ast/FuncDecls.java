/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

import java.util.List;

/**
 * Represents function declarations.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * func_decls: FUNCTIONS LBRACE (func_decl)* RBRACE;
 * }</pre>
 */
@NullMarked
public class FuncDecls extends BaseAstNode {
    private final List<FuncDecl> decls;

    public FuncDecls(Position position, List<FuncDecl> decls) {
        super(position);
        this.decls = decls;
        for (FuncDecl d : decls) {
            setChildParent(d);
        }
    }

    public List<FuncDecl> getDecls() {
        return decls;
    }
}
