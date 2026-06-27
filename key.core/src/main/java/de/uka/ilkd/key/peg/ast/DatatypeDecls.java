/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

import java.util.List;

/**
 * Represents datatype declarations.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * datatype_decls: DATATYPES LBRACE datatype_decl* RBRACE;
 * }</pre>
 */
@NullMarked
public class DatatypeDecls extends BaseAstNode {
    private final List<DatatypeDecl> decls;

    public DatatypeDecls(Position position, List<DatatypeDecl> decls) {
        super(position);
        this.decls = decls;
        for (DatatypeDecl d : decls) {
            setChildParent(d);
        }
    }

    public List<DatatypeDecl> getDecls() {
        return decls;
    }
}