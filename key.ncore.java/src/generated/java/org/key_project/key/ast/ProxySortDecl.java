package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class ProxySortDecl extends BaseAstNode {

    @Nullable
    private String docComment;

    private List<String> sortNames;

    private KeyJavaType javaType;

    @Nullable
    private Position position;

    @Nullable()
    public String docComment() {
        return docComment;
    }

    public ProxySortDecl setDocComment(@Nullable() String value) {
        docComment = value;
        return this;
    }

    public List<String> sortNames() {
        return sortNames;
    }

    public ProxySortDecl setSortNames(List<String> value) {
        sortNames = value;
        return this;
    }

    public KeyJavaType javaType() {
        return javaType;
    }

    public ProxySortDecl setJavaType(KeyJavaType value) {
        javaType = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public ProxySortDecl setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public ProxySortDecl(@Nullable String docComment, List<String> sortNames, KeyJavaType javaType, @Nullable Position position) {
        this.docComment = docComment;
        this.sortNames = Objects.requireNonNull(sortNames);
        this.javaType = Objects.requireNonNull(javaType);
        this.position = position;
    }

    public ProxySortDecl(List<String> sortNames, KeyJavaType javaType) {
        this.docComment = null;
        this.sortNames = Objects.requireNonNull(sortNames);
        this.javaType = Objects.requireNonNull(javaType);
        this.position = null;
    }

    public ProxySortDecl(ProxySortDecl other) {
        this(other.docComment, other.sortNames, other.javaType, other.position);
    }

    public final static class Builder {

        @Nullable()
        public String docComment;

        @Nullable()
        public List<String> sortNames;

        @Nullable()
        public KeyJavaType javaType;

        @Nullable()
        public Position position;

        public ProxySortDecl build() {
            return new ProxySortDecl(docComment, sortNames, javaType, position);
        }

        public Builder docComment(String docComment) {
            this.docComment = docComment;
            return this;
        }

        public Builder sortNames(List<String> sortNames) {
            this.sortNames = sortNames;
            return this;
        }

        public Builder javaType(KeyJavaType javaType) {
            this.javaType = javaType;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder sortNames(String sortNames) {
            if (this.sortNames == null)
                this.sortNames = new ArrayList<>();
            this.sortNames.add(sortNames);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.docComment = docComment;
        b.sortNames = sortNames;
        b.javaType = javaType;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof ProxySortDecl that))
            return false;
        return Objects.equals(docComment, that.docComment) && Objects.equals(sortNames, that.sortNames) && Objects.equals(javaType, that.javaType) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "ProxySortDecl[docComment=%s, sortNames=%s, javaType=%s, position=%s]".formatted(docComment, sortNames, javaType, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(docComment, sortNames, javaType, position);
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
