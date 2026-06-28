package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class AbstractSortDeclimplements extends BaseAstNode {

    @Nullable
    private String docComment;

    private boolean isAbstract;

    private List<SimpleIdentDots> sortIds;

    @Nullable
    private FormalSortParamDecls formalSortParamDecls;

    @Nullable
    private ExtendsSorts extendsSorts;

    @Nullable
    private Position position;

    @Nullable()
    public String docComment() {
        return docComment;
    }

    public AbstractSortDeclimplements setDocComment(@Nullable() String value) {
        docComment = value;
        return this;
    }

    public boolean isAbstract() {
        return isAbstract;
    }

    public AbstractSortDeclimplements setIsAbstract(boolean value) {
        isAbstract = value;
        return this;
    }

    public List<SimpleIdentDots> sortIds() {
        return sortIds;
    }

    public AbstractSortDeclimplements setSortIds(List<SimpleIdentDots> value) {
        sortIds = value;
        return this;
    }

    @Nullable()
    public FormalSortParamDecls formalSortParamDecls() {
        return formalSortParamDecls;
    }

    public AbstractSortDeclimplements setFormalSortParamDecls(@Nullable() FormalSortParamDecls value) {
        formalSortParamDecls = value;
        return this;
    }

    @Nullable()
    public ExtendsSorts extendsSorts() {
        return extendsSorts;
    }

    public AbstractSortDeclimplements setExtendsSorts(@Nullable() ExtendsSorts value) {
        extendsSorts = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public AbstractSortDeclimplements setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public AbstractSortDeclimplements(@Nullable String docComment, boolean isAbstract, List<SimpleIdentDots> sortIds, @Nullable FormalSortParamDecls formalSortParamDecls, @Nullable ExtendsSorts extendsSorts, @Nullable Position position) {
        this.docComment = docComment;
        this.isAbstract = Objects.requireNonNull(isAbstract);
        this.sortIds = Objects.requireNonNull(sortIds);
        this.formalSortParamDecls = formalSortParamDecls;
        this.extendsSorts = extendsSorts;
        this.position = position;
    }

    public AbstractSortDeclimplements(boolean isAbstract, List<SimpleIdentDots> sortIds) {
        this.docComment = null;
        this.isAbstract = Objects.requireNonNull(isAbstract);
        this.sortIds = Objects.requireNonNull(sortIds);
        this.formalSortParamDecls = null;
        this.extendsSorts = null;
        this.position = null;
    }

    public AbstractSortDeclimplements(AbstractSortDeclimplements other) {
        this(other.docComment, other.isAbstract, other.sortIds, other.formalSortParamDecls, other.extendsSorts, other.position);
    }

    public final static class Builder {

        @Nullable()
        public String docComment;

        @Nullable()
        public boolean isAbstract;

        @Nullable()
        public List<SimpleIdentDots> sortIds;

        @Nullable()
        public FormalSortParamDecls formalSortParamDecls;

        @Nullable()
        public ExtendsSorts extendsSorts;

        @Nullable()
        public Position position;

        public AbstractSortDeclimplements build() {
            return new AbstractSortDeclimplements(docComment, isAbstract, sortIds, formalSortParamDecls, extendsSorts, position);
        }

        public Builder docComment(String docComment) {
            this.docComment = docComment;
            return this;
        }

        public Builder isAbstract(boolean isAbstract) {
            this.isAbstract = isAbstract;
            return this;
        }

        public Builder sortIds(List<SimpleIdentDots> sortIds) {
            this.sortIds = sortIds;
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
        b.docComment = docComment;
        b.isAbstract = isAbstract;
        b.sortIds = sortIds;
        b.formalSortParamDecls = formalSortParamDecls;
        b.extendsSorts = extendsSorts;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof AbstractSortDeclimplements that))
            return false;
        return Objects.equals(docComment, that.docComment) && Objects.equals(isAbstract, that.isAbstract) && Objects.equals(sortIds, that.sortIds) && Objects.equals(formalSortParamDecls, that.formalSortParamDecls) && Objects.equals(extendsSorts, that.extendsSorts) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "AbstractSortDeclimplements[docComment=%s, isAbstract=%s, sortIds=%s, formalSortParamDecls=%s, extendsSorts=%s, position=%s]".formatted(docComment, isAbstract, sortIds, formalSortParamDecls, extendsSorts, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(docComment, isAbstract, sortIds, formalSortParamDecls, extendsSorts, position);
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
