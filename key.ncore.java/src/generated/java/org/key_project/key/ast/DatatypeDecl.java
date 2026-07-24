package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class DatatypeDecl extends BaseAstNode {

    @Nullable
    private String docComment;

    private boolean isFree;

    private SimpleIdentDots name;

    @Nullable
    private FormalSortParamDecls formalSortParams;

    private List<DatatypeConstructor> constructors;

    @Nullable
    private Position position;

    @Nullable()
    public String docComment() {
        return docComment;
    }

    public DatatypeDecl setDocComment(@Nullable() String value) {
        docComment = value;
        return this;
    }

    public boolean isFree() {
        return isFree;
    }

    public DatatypeDecl setIsFree(boolean value) {
        isFree = value;
        return this;
    }

    public SimpleIdentDots name() {
        return name;
    }

    public DatatypeDecl setName(SimpleIdentDots value) {
        name = value;
        return this;
    }

    @Nullable()
    public FormalSortParamDecls formalSortParams() {
        return formalSortParams;
    }

    public DatatypeDecl setFormalSortParams(@Nullable() FormalSortParamDecls value) {
        formalSortParams = value;
        return this;
    }

    public List<DatatypeConstructor> constructors() {
        return constructors;
    }

    public DatatypeDecl setConstructors(List<DatatypeConstructor> value) {
        constructors = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public DatatypeDecl setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public DatatypeDecl(@Nullable String docComment, boolean isFree, SimpleIdentDots name, @Nullable FormalSortParamDecls formalSortParams, List<DatatypeConstructor> constructors, @Nullable Position position) {
        this.docComment = docComment;
        this.isFree = Objects.requireNonNull(isFree);
        this.name = Objects.requireNonNull(name);
        this.formalSortParams = formalSortParams;
        this.constructors = Objects.requireNonNull(constructors);
        this.position = position;
    }

    public DatatypeDecl(boolean isFree, SimpleIdentDots name, List<DatatypeConstructor> constructors) {
        this.docComment = null;
        this.isFree = Objects.requireNonNull(isFree);
        this.name = Objects.requireNonNull(name);
        this.formalSortParams = null;
        this.constructors = Objects.requireNonNull(constructors);
        this.position = null;
    }

    public DatatypeDecl(DatatypeDecl other) {
        this(other.docComment, other.isFree, other.name, other.formalSortParams, other.constructors, other.position);
    }

    public final static class Builder {

        @Nullable()
        public String docComment;

        @Nullable()
        public boolean isFree;

        @Nullable()
        public SimpleIdentDots name;

        @Nullable()
        public FormalSortParamDecls formalSortParams;

        @Nullable()
        public List<DatatypeConstructor> constructors;

        @Nullable()
        public Position position;

        public DatatypeDecl build() {
            return new DatatypeDecl(docComment, isFree, name, formalSortParams, constructors, position);
        }

        public Builder docComment(String docComment) {
            this.docComment = docComment;
            return this;
        }

        public Builder isFree(boolean isFree) {
            this.isFree = isFree;
            return this;
        }

        public Builder name(SimpleIdentDots name) {
            this.name = name;
            return this;
        }

        public Builder formalSortParams(FormalSortParamDecls formalSortParams) {
            this.formalSortParams = formalSortParams;
            return this;
        }

        public Builder constructors(List<DatatypeConstructor> constructors) {
            this.constructors = constructors;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder constructors(DatatypeConstructor constructors) {
            if (this.constructors == null)
                this.constructors = new ArrayList<>();
            this.constructors.add(constructors);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.docComment = docComment;
        b.isFree = isFree;
        b.name = name;
        b.formalSortParams = formalSortParams;
        b.constructors = constructors;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof DatatypeDecl that))
            return false;
        return Objects.equals(docComment, that.docComment) && Objects.equals(isFree, that.isFree) && Objects.equals(name, that.name) && Objects.equals(formalSortParams, that.formalSortParams) && Objects.equals(constructors, that.constructors) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "DatatypeDecl[docComment=%s, isFree=%s, name=%s, formalSortParams=%s, constructors=%s, position=%s]".formatted(docComment, isFree, name, formalSortParams, constructors, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(docComment, isFree, name, formalSortParams, constructors, position);
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
