package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class GenericSortDecl extends BaseAstNode {

    @Nullable
    private String docComment;

    private List<String> sortNames;

    @Nullable
    private ExtendsSorts extendsSorts;

    @Nullable
    private FormalSortParamDecls formalParams;

    @Nullable
    private Position position;

    @Nullable()
    public String docComment() {
        return docComment;
    }

    public GenericSortDecl setDocComment(@Nullable() String value) {
        docComment = value;
        return this;
    }

    public List<String> sortNames() {
        return sortNames;
    }

    public GenericSortDecl setSortNames(List<String> value) {
        sortNames = value;
        return this;
    }

    @Nullable()
    public ExtendsSorts extendsSorts() {
        return extendsSorts;
    }

    public GenericSortDecl setExtendsSorts(@Nullable() ExtendsSorts value) {
        extendsSorts = value;
        return this;
    }

    @Nullable()
    public FormalSortParamDecls formalParams() {
        return formalParams;
    }

    public GenericSortDecl setFormalParams(@Nullable() FormalSortParamDecls value) {
        formalParams = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public GenericSortDecl setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public GenericSortDecl(@Nullable String docComment, List<String> sortNames, @Nullable ExtendsSorts extendsSorts, @Nullable FormalSortParamDecls formalParams, @Nullable Position position) {
        this.docComment = docComment;
        this.sortNames = Objects.requireNonNull(sortNames);
        this.extendsSorts = extendsSorts;
        this.formalParams = formalParams;
        this.position = position;
    }

    public GenericSortDecl(List<String> sortNames) {
        this.docComment = null;
        this.sortNames = Objects.requireNonNull(sortNames);
        this.extendsSorts = null;
        this.formalParams = null;
        this.position = null;
    }

    public GenericSortDecl(GenericSortDecl other) {
        this(other.docComment, other.sortNames, other.extendsSorts, other.formalParams, other.position);
    }

    public final static class Builder {

        @Nullable()
        public String docComment;

        @Nullable()
        public List<String> sortNames;

        @Nullable()
        public ExtendsSorts extendsSorts;

        @Nullable()
        public FormalSortParamDecls formalParams;

        @Nullable()
        public Position position;

        public GenericSortDecl build() {
            return new GenericSortDecl(docComment, sortNames, extendsSorts, formalParams, position);
        }

        public Builder docComment(String docComment) {
            this.docComment = docComment;
            return this;
        }

        public Builder sortNames(List<String> sortNames) {
            this.sortNames = sortNames;
            return this;
        }

        public Builder extendsSorts(ExtendsSorts extendsSorts) {
            this.extendsSorts = extendsSorts;
            return this;
        }

        public Builder formalParams(FormalSortParamDecls formalParams) {
            this.formalParams = formalParams;
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
        b.extendsSorts = extendsSorts;
        b.formalParams = formalParams;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof GenericSortDecl that))
            return false;
        return Objects.equals(docComment, that.docComment) && Objects.equals(sortNames, that.sortNames) && Objects.equals(extendsSorts, that.extendsSorts) && Objects.equals(formalParams, that.formalParams) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "GenericSortDecl[docComment=%s, sortNames=%s, extendsSorts=%s, formalParams=%s, position=%s]".formatted(docComment, sortNames, extendsSorts, formalParams, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(docComment, sortNames, extendsSorts, formalParams, position);
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
