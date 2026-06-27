/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import java.util.List;

/**
 * Represents a datatype declaration.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * datatype_decl: doc=DOC_COMMENT? (FREE)? name=simple_ident formal_sort_param_decls? EQUALS datatype_constructor (OR datatype_constructor)* SEMI;
 * }</pre>
 */
@NullMarked
public class DatatypeDecl extends BaseAstNode {
    private final @Nullable String docComment;
    private final boolean isFree;
    private final SimpleIdentDots name;
    private final @Nullable FormalSortParamDecls formalSortParams;
    private final List<DatatypeConstructor> constructors;

    public DatatypeDecl(Position position, @Nullable String docComment, boolean isFree,
                        SimpleIdentDots name, @Nullable FormalSortParamDecls formalSortParams,
                        List<DatatypeConstructor> constructors) {
        super(position);
        this.docComment = docComment;
        this.isFree = isFree;
        this.name = name;
        this.formalSortParams = formalSortParams;
        this.constructors = constructors;
        setChildParent(name);
        if (formalSortParams != null) setChildParent(formalSortParams);
        for (DatatypeConstructor c : constructors) {
            setChildParent(c);
        }
    }

    public @Nullable String getDocComment() {
        return docComment;
    }

    public boolean isFree() {
        return isFree;
    }

    public SimpleIdentDots getName() {
        return name;
    }

    public @Nullable FormalSortParamDecls getFormalSortParams() {
        return formalSortParams;
    }

    public List<DatatypeConstructor> getConstructors() {
        return constructors;
    }
}