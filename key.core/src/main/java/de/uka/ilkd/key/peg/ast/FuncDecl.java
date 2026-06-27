/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Represents a function declaration.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * func_decl: doc=DOC_COMMENT? (UNIQUE)? retSort = sortId func_name = funcpred_name formal_sort_param_decls? whereToBind=where_to_bind? argSorts = arg_sorts SEMI;
 * }</pre>
 */
@NullMarked
public class FuncDecl extends BaseAstNode {
    private final @Nullable String docComment;
    private final boolean isUnique;
    private final SortId returnSort;
    private final FuncPredName name;
    private final @Nullable FormalSortParamDecls formalSortParams;
    private final @Nullable WhereToBind whereToBind;
    private final ArgSorts argSorts;

    public FuncDecl(Position position, @Nullable String docComment, boolean isUnique, SortId returnSort,
                    FuncPredName name, @Nullable FormalSortParamDecls formalSortParams,
                    @Nullable WhereToBind whereToBind, ArgSorts argSorts) {
        super(position);
        this.docComment = docComment;
        this.isUnique = isUnique;
        this.returnSort = returnSort;
        this.name = name;
        this.formalSortParams = formalSortParams;
        this.whereToBind = whereToBind;
        this.argSorts = argSorts;
        setChildParent(returnSort);
        setChildParent(name);
        if (formalSortParams != null) setChildParent(formalSortParams);
        if (whereToBind != null) setChildParent(whereToBind);
        setChildParent(argSorts);
    }

    public @Nullable String getDocComment() {
        return docComment;
    }

    public boolean isUnique() {
        return isUnique;
    }

    public SortId getReturnSort() {
        return returnSort;
    }

    public FuncPredName getName() {
        return name;
    }

    public @Nullable FormalSortParamDecls getFormalSortParams() {
        return formalSortParams;
    }

    public @Nullable WhereToBind getWhereToBind() {
        return whereToBind;
    }

    public ArgSorts getArgSorts() {
        return argSorts;
    }
}