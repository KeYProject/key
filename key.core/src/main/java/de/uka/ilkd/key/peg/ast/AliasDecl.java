/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Represents an alias sort declaration.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * ALIAS simple_ident_dots EQUALS sortId SEMI;
 * }</pre>
 */
@NullMarked
public class AliasDecl extends BaseAstNode implements OneSortDecl {
    private final @Nullable String docComment;
    private final SimpleIdentDots aliasName;
    private final SortId targetSort;

    public AliasDecl(Position position, @Nullable String docComment, SimpleIdentDots aliasName, SortId targetSort) {
        super(position);
        this.docComment = docComment;
        this.aliasName = aliasName;
        this.targetSort = targetSort;
        setChildParent(aliasName);
        setChildParent(targetSort);
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public @Nullable String getDocComment() {
        return docComment;
    }

    public SimpleIdentDots getAliasName() {
        return aliasName;
    }

    public SortId getTargetSort() {
        return targetSort;
    }
}