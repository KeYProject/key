/* This file is part of KeY - https://project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Represents a predicate declaration.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * pred_decl: doc=DOC_COMMENT? pred_name = funcpred_name formal_sort_param_decls? (whereToBind=where_to_bind)? argSorts=arg_sorts SEMI;
 * }</pre>
 */
@NullMarked
public class PredDecl extends BaseAstNode {
    private final @Nullable String docComment;
    private final FuncPredName name;
    private final @Nullable FormalSortParamDecls formalSortParams;
    private final @Nullable WhereToBind whereToBind;
    private final ArgSorts argSorts;

    public PredDecl(Position position, @Nullable String docComment, FuncPredName name,
                    @Nullable FormalSortParamDecls formalSortParams, @Nullable WhereToBind whereToBind, ArgSorts argSorts) {
        super(position);
        this.docComment = docComment;
        this.name = name;
        this.formalSortParams = formalSortParams;
        this.whereToBind = whereToBind;
        this.argSorts = argSorts;
        setChildParent(name);
        if (formalSortParams != null) setChildParent(formalSortParams);
        if (whereToBind != null) setChildParent(whereToBind);
        setChildParent(argSorts);
    }

    public @Nullable String getDocComment() {
        return docComment;
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