package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class FuncDecl extends BaseAstNode {

    @Nullable
    private String docComment;

    private boolean isUnique;

    private SortId returnSort;

    private FuncPredName name;

    @Nullable
    private FormalSortParamDecls formalSortParams;

    @Nullable
    private WhereToBind whereToBind;

    private ArgSorts argSorts;

    @Nullable
    private Position position;

    @Nullable()
    public String docComment() {
        return docComment;
    }

    public FuncDecl setDocComment(@Nullable() String value) {
        docComment = value;
        return this;
    }

    public boolean isUnique() {
        return isUnique;
    }

    public FuncDecl setIsUnique(boolean value) {
        isUnique = value;
        return this;
    }

    public SortId returnSort() {
        return returnSort;
    }

    public FuncDecl setReturnSort(SortId value) {
        returnSort = value;
        return this;
    }

    public FuncPredName name() {
        return name;
    }

    public FuncDecl setName(FuncPredName value) {
        name = value;
        return this;
    }

    @Nullable()
    public FormalSortParamDecls formalSortParams() {
        return formalSortParams;
    }

    public FuncDecl setFormalSortParams(@Nullable() FormalSortParamDecls value) {
        formalSortParams = value;
        return this;
    }

    @Nullable()
    public WhereToBind whereToBind() {
        return whereToBind;
    }

    public FuncDecl setWhereToBind(@Nullable() WhereToBind value) {
        whereToBind = value;
        return this;
    }

    public ArgSorts argSorts() {
        return argSorts;
    }

    public FuncDecl setArgSorts(ArgSorts value) {
        argSorts = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public FuncDecl setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public FuncDecl(@Nullable String docComment, boolean isUnique, SortId returnSort, FuncPredName name, @Nullable FormalSortParamDecls formalSortParams, @Nullable WhereToBind whereToBind, ArgSorts argSorts, @Nullable Position position) {
        this.docComment = docComment;
        this.isUnique = Objects.requireNonNull(isUnique);
        this.returnSort = Objects.requireNonNull(returnSort);
        this.name = Objects.requireNonNull(name);
        this.formalSortParams = formalSortParams;
        this.whereToBind = whereToBind;
        this.argSorts = Objects.requireNonNull(argSorts);
        this.position = position;
    }

    public FuncDecl(boolean isUnique, SortId returnSort, FuncPredName name, ArgSorts argSorts) {
        this.docComment = null;
        this.isUnique = Objects.requireNonNull(isUnique);
        this.returnSort = Objects.requireNonNull(returnSort);
        this.name = Objects.requireNonNull(name);
        this.formalSortParams = null;
        this.whereToBind = null;
        this.argSorts = Objects.requireNonNull(argSorts);
        this.position = null;
    }

    public FuncDecl(FuncDecl other) {
        this(other.docComment, other.isUnique, other.returnSort, other.name, other.formalSortParams, other.whereToBind, other.argSorts, other.position);
    }

    public final static class Builder {

        @Nullable()
        public String docComment;

        @Nullable()
        public boolean isUnique;

        @Nullable()
        public SortId returnSort;

        @Nullable()
        public FuncPredName name;

        @Nullable()
        public FormalSortParamDecls formalSortParams;

        @Nullable()
        public WhereToBind whereToBind;

        @Nullable()
        public ArgSorts argSorts;

        @Nullable()
        public Position position;

        public FuncDecl build() {
            return new FuncDecl(docComment, isUnique, returnSort, name, formalSortParams, whereToBind, argSorts, position);
        }

        public Builder docComment(String docComment) {
            this.docComment = docComment;
            return this;
        }

        public Builder isUnique(boolean isUnique) {
            this.isUnique = isUnique;
            return this;
        }

        public Builder returnSort(SortId returnSort) {
            this.returnSort = returnSort;
            return this;
        }

        public Builder name(FuncPredName name) {
            this.name = name;
            return this;
        }

        public Builder formalSortParams(FormalSortParamDecls formalSortParams) {
            this.formalSortParams = formalSortParams;
            return this;
        }

        public Builder whereToBind(WhereToBind whereToBind) {
            this.whereToBind = whereToBind;
            return this;
        }

        public Builder argSorts(ArgSorts argSorts) {
            this.argSorts = argSorts;
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
        b.isUnique = isUnique;
        b.returnSort = returnSort;
        b.name = name;
        b.formalSortParams = formalSortParams;
        b.whereToBind = whereToBind;
        b.argSorts = argSorts;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof FuncDecl that))
            return false;
        return Objects.equals(docComment, that.docComment) && Objects.equals(isUnique, that.isUnique) && Objects.equals(returnSort, that.returnSort) && Objects.equals(name, that.name) && Objects.equals(formalSortParams, that.formalSortParams) && Objects.equals(whereToBind, that.whereToBind) && Objects.equals(argSorts, that.argSorts) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "FuncDecl[docComment=%s, isUnique=%s, returnSort=%s, name=%s, formalSortParams=%s, whereToBind=%s, argSorts=%s, position=%s]".formatted(docComment, isUnique, returnSort, name, formalSortParams, whereToBind, argSorts, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(docComment, isUnique, returnSort, name, formalSortParams, whereToBind, argSorts, position);
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
