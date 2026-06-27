/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import java.util.List;

/**
 * Represents a generic sort declaration.
 * Corresponds to the grammar rule for GENERIC kind in one_sort_decl.
 */
@NullMarked
public class GenericSortDecl extends BaseAstNode implements OneSortDecl {
    private final @Nullable String docComment;
    private final List<String> sortNames;
    private final @Nullable ExtendsSorts extendsSorts;
    private final @Nullable FormalSortParamDecls formalParams;

    public GenericSortDecl(Position position,
                           @Nullable String docComment,
                           List<String> sortNames,
                           @Nullable ExtendsSorts extendsSorts,
                           @Nullable FormalSortParamDecls formalParams) {
        super(position);
        this.docComment = docComment;
        this.sortNames = sortNames;
        this.extendsSorts = extendsSorts;
        this.formalParams = formalParams;
        setChildParent(extendsSorts);
        setChildParent(formalParams);
    }

    public @Nullable String getDocComment() {
        return docComment;
    }

    public List<String> getSortNames() {
        return sortNames;
    }

    public @Nullable ExtendsSorts getExtendsSorts() {
        return extendsSorts;
    }

    public @Nullable FormalSortParamDecls getFormalParams() {
        return formalParams;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}