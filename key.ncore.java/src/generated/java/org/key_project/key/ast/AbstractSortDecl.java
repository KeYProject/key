package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class AbstractSortDecl extends BaseAstNode {

    private boolean isAbstract;

    private List<SimpleIdentDots> sortIds;

    @Nullable
    private String docComment;

    @Nullable
    private FormalSortParamDecls formalSortParamDecls;

    @Nullable
    private ExtendsSorts extendsSorts;

    @Nullable
    private Position position;

    public boolean isAbstract() {
        return isAbstract;
    }

    public AbstractSortDecl setIsAbstract(boolean value) {
        isAbstract = value;
        return this;
    }

    public List<SimpleIdentDots> sortIds() {
        return sortIds;
    }

    public AbstractSortDecl setSortIds(List<SimpleIdentDots> value) {
        sortIds = value;
        return this;
    }

    @Nullable()
    public String docComment() {
        return docComment;
    }

    public AbstractSortDecl setDocComment(@Nullable() String value) {
        docComment = value;
        return this;
    }

    @Nullable()
    public FormalSortParamDecls formalSortParamDecls() {
        return formalSortParamDecls;
    }

    public AbstractSortDecl setFormalSortParamDecls(@Nullable() FormalSortParamDecls value) {
        formalSortParamDecls = value;
        return this;
    }

    @Nullable()
    public ExtendsSorts extendsSorts() {
        return extendsSorts;
    }

    public AbstractSortDecl setExtendsSorts(@Nullable() ExtendsSorts value) {
        extendsSorts = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public AbstractSortDecl setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public AbstractSortDecl(boolean isAbstract, List<SimpleIdentDots> sortIds, @Nullable String docComment, @Nullable FormalSortParamDecls formalSortParamDecls, @Nullable ExtendsSorts extendsSorts, @Nullable Position position) {
        this.isAbstract = Objects.requireNonNull(isAbstract);
        this.sortIds = Objects.requireNonNull(sortIds);
        this.docComment = docComment;
        this.formalSortParamDecls = formalSortParamDecls;
        this.extendsSorts = extendsSorts;
        this.position = position;
    }

    public AbstractSortDecl(boolean isAbstract, List<SimpleIdentDots> sortIds) {
        this.isAbstract = Objects.requireNonNull(isAbstract);
        this.sortIds = Objects.requireNonNull(sortIds);
        this.docComment = null;
        this.formalSortParamDecls = null;
        this.extendsSorts = null;
        this.position = null;
    }

    public AbstractSortDecl(AbstractSortDecl other) {
        this(other.isAbstract, other.sortIds, other.docComment, other.formalSortParamDecls, other.extendsSorts, other.position);
    }

    public final static class Builder {

        @Nullable()
        public boolean isAbstract;

        @Nullable()
        public List<SimpleIdentDots> sortIds;

        @Nullable()
        public String docComment;

        @Nullable()
        public FormalSortParamDecls formalSortParamDecls;

        @Nullable()
        public ExtendsSorts extendsSorts;

        @Nullable()
        public Position position;

        public AbstractSortDecl build() {
            return new AbstractSortDecl(isAbstract, sortIds, docComment, formalSortParamDecls, extendsSorts, position);
        }

        public Builder isAbstract(boolean isAbstract) {
            this.isAbstract = isAbstract;
            return this;
        }

        public Builder sortIds(List<SimpleIdentDots> sortIds) {
            this.sortIds = sortIds;
            return this;
        }

        public Builder docComment(String docComment) {
            this.docComment = docComment;
            return this;
        }

        public Builder formalSortParamDecls(FormalSortParamDecls formalSortParamDecls) {
            this.formalSortParamDecls = formalSortParamDecls;
            return this;
        }

        public Builder extendsSorts(ExtendsSorts extendsSorts) {
            this.extendsSorts = extendsSorts;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder sortIds(SimpleIdentDots sortIds) {
            if (this.sortIds == null)
                this.sortIds = new ArrayList<>();
            this.sortIds.add(sortIds);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.isAbstract = isAbstract;
        b.sortIds = sortIds;
        b.docComment = docComment;
        b.formalSortParamDecls = formalSortParamDecls;
        b.extendsSorts = extendsSorts;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof AbstractSortDecl that))
            return false;
        return Objects.equals(isAbstract, that.isAbstract) && Objects.equals(sortIds, that.sortIds) && Objects.equals(docComment, that.docComment) && Objects.equals(formalSortParamDecls, that.formalSortParamDecls) && Objects.equals(extendsSorts, that.extendsSorts) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "AbstractSortDecl[isAbstract=%s, sortIds=%s, docComment=%s, formalSortParamDecls=%s, extendsSorts=%s, position=%s]".formatted(isAbstract, sortIds, docComment, formalSortParamDecls, extendsSorts, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(isAbstract, sortIds, docComment, formalSortParamDecls, extendsSorts, position);
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
