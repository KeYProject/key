/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import java.util.List;

/**
 * Represents a proxy sort declaration.
 * Corresponds to the grammar rule for PROXY kind in one_sort_decl.
 */
@NullMarked
public class ProxySortDecl extends BaseAstNode implements OneSortDecl {
    private final @Nullable String docComment;
    private final List<String> sortNames;
    private final KeyJavaType javaType;

    public ProxySortDecl(Position position,
                         @Nullable String docComment,
                         List<String> sortNames,
                         KeyJavaType javaType) {
        super(position);
        this.docComment = docComment;
        this.sortNames = sortNames;
        this.javaType = javaType;
        setChildParent(javaType);
    }

    public @Nullable String getDocComment() {
        return docComment;
    }

    public List<String> getSortNames() {
        return sortNames;
    }

    public KeyJavaType getJavaType() {
        return javaType;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}