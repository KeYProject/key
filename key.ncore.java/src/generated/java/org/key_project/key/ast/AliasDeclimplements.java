package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class AliasDeclimplements extends BaseAstNode {

    @Nullable
    private String docComment;

    private SimpleIdentDots aliasName;

    private SortId targetSort;

    @Nullable
    private Position position;

    @Nullable()
    public String docComment() {
        return docComment;
    }

    public AliasDeclimplements setDocComment(@Nullable() String value) {
        docComment = value;
        return this;
    }

    public SimpleIdentDots aliasName() {
        return aliasName;
    }

    public AliasDeclimplements setAliasName(SimpleIdentDots value) {
        aliasName = value;
        return this;
    }

    public SortId targetSort() {
        return targetSort;
    }

    public AliasDeclimplements setTargetSort(SortId value) {
        targetSort = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public AliasDeclimplements setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public AliasDeclimplements(@Nullable String docComment, SimpleIdentDots aliasName, SortId targetSort, @Nullable Position position) {
        this.docComment = docComment;
        this.aliasName = Objects.requireNonNull(aliasName);
        this.targetSort = Objects.requireNonNull(targetSort);
        this.position = position;
    }

    public AliasDeclimplements(SimpleIdentDots aliasName, SortId targetSort) {
        this.docComment = null;
        this.aliasName = Objects.requireNonNull(aliasName);
        this.targetSort = Objects.requireNonNull(targetSort);
        this.position = null;
    }

    public AliasDeclimplements(AliasDeclimplements other) {
        this(other.docComment, other.aliasName, other.targetSort, other.position);
    }

    public final static class Builder {

        @Nullable()
        public String docComment;

        @Nullable()
        public SimpleIdentDots aliasName;

        @Nullable()
        public SortId targetSort;

        @Nullable()
        public Position position;

        public AliasDeclimplements build() {
            return new AliasDeclimplements(docComment, aliasName, targetSort, position);
        }

        public Builder docComment(String docComment) {
            this.docComment = docComment;
            return this;
        }

        public Builder aliasName(SimpleIdentDots aliasName) {
            this.aliasName = aliasName;
            return this;
        }

        public Builder targetSort(SortId targetSort) {
            this.targetSort = targetSort;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.docComment = docComment;
        b.aliasName = aliasName;
        b.targetSort = targetSort;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof AliasDeclimplements that))
            return false;
        return Objects.equals(docComment, that.docComment) && Objects.equals(aliasName, that.aliasName) && Objects.equals(targetSort, that.targetSort) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "AliasDeclimplements[docComment=%s, aliasName=%s, targetSort=%s, position=%s]".formatted(docComment, aliasName, targetSort, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(docComment, aliasName, targetSort, position);
    }

    public <R> R accept(org.key_project.key.ast.visitor.Visitor<R> visitor) {
        return visitor.visit(this);
    }

    public <R, A> R accept(org.key_project.key.ast.visitor.ArgVisitor<R, A> visitor, A arg) {
        return visitor.visit(this, arg);
    }

    public void accept(org.key_project.key.ast.visitor.VoidVisitor visitor) {
        visitor.visit(this);
    }
}
