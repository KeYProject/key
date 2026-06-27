/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

import java.util.List;

/**
 * Represents predicate declarations.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * pred_decls: PREDICATES LBRACE (pred_decl)* RBRACE;
 * }</pre>
 */
@NullMarked
public class PredDecls extends BaseAstNode {
    private final List<PredDecl> decls;

    public PredDecls(Position position, List<PredDecl> decls) {
        super(position);
        this.decls = decls;
        for (PredDecl d : decls) {
            setChildParent(d);
        }
    }

    public List<PredDecl> getDecls() {
        return decls;
    }
}
