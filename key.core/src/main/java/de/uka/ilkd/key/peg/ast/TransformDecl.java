/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Represents a transformer declaration.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * transform_decl: doc=DOC_COMMENT? (retSort = sortId | FORMULA) trans_name=funcpred_name argSorts=arg_sorts_or_formula SEMI;
 * }</pre>
 */
@NullMarked
public class TransformDecl extends BaseAstNode {
    private final @Nullable String docComment;
    private final @Nullable SortId returnSort;
    private final boolean isFormula;
    private final FuncPredName name;
    private final ArgSortsOrFormula argSorts;

    public TransformDecl(Position position, @Nullable String docComment, @Nullable SortId returnSort,
                         boolean isFormula, FuncPredName name, ArgSortsOrFormula argSorts) {
        super(position);
        this.docComment = docComment;
        this.returnSort = returnSort;
        this.isFormula = isFormula;
        this.name = name;
        this.argSorts = argSorts;
        if (returnSort != null) setChildParent(returnSort);
        setChildParent(name);
        setChildParent(argSorts);
    }

    public @Nullable String getDocComment() {
        return docComment;
    }

    public @Nullable SortId getReturnSort() {
        return returnSort;
    }

    public boolean isFormula() {
        return isFormula;
    }

    public FuncPredName getName() {
        return name;
    }

    public ArgSortsOrFormula getArgSorts() {
        return argSorts;
    }
}