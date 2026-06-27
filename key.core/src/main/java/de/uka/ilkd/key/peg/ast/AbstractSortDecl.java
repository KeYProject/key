/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import java.util.List;

/**
 * Represents an abstract sort declaration.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * ABSTRACT? (sortIds=simple_ident_dots_comma_list | parametric_sort_decl) (EXTENDS sortExt=extends_sorts)? SEMI;
 * }</pre>
 */
@NullMarked
public class AbstractSortDecl extends BaseAstNode implements OneSortDecl {
    private final @Nullable String docComment;
    private final boolean isAbstract;
    private final List<SimpleIdentDots> sortIds;
    private final @Nullable FormalSortParamDecls formalSortParamDecls;
    private final @Nullable ExtendsSorts extendsSorts;

    public AbstractSortDecl(Position position, @Nullable String docComment, boolean isAbstract,
                            List<SimpleIdentDots> sortIds, @Nullable FormalSortParamDecls formalSortParamDecls,
                            @Nullable ExtendsSorts extendsSorts) {
        super(position);
        this.docComment = docComment;
        this.isAbstract = isAbstract;
        this.sortIds = sortIds;
        this.formalSortParamDecls = formalSortParamDecls;
        this.extendsSorts = extendsSorts;
        for (SimpleIdentDots id : sortIds) {
            setChildParent(id);
        }
        if (formalSortParamDecls != null) {
            setChildParent(formalSortParamDecls);
        }
        if (extendsSorts != null) {
            setChildParent(extendsSorts);
        }
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public @Nullable String getDocComment() {
        return docComment;
    }

    public boolean isAbstract() {
        return isAbstract;
    }

    public List<SimpleIdentDots> getSortIds() {
        return sortIds;
    }

    public @Nullable FormalSortParamDecls getFormalSortParamDecls() {
        return formalSortParamDecls;
    }

    public @Nullable ExtendsSorts getExtendsSorts() {
        return extendsSorts;
    }
}