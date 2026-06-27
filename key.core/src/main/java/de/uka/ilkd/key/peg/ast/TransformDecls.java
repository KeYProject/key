/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

import java.util.List;

/**
 * Represents transformer declarations.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * transform_decls: TRANSFORMERS LBRACE (transform_decl)* RBRACE;
 * }</pre>
 */
@NullMarked
public class TransformDecls extends BaseAstNode {
    private final List<TransformDecl> decls;

    public TransformDecls(Position position, List<TransformDecl> decls) {
        super(position);
        this.decls = decls;
        for (TransformDecl d : decls) {
            setChildParent(d);
        }
    }

    public List<TransformDecl> getDecls() {
        return decls;
    }
}