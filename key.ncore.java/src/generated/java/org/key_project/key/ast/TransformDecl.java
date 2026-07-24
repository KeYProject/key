package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class TransformDecl extends BaseAstNode {

    @Nullable
    private String docComment;

    @Nullable
    private SortId returnSort;

    private boolean isFormula;

    private FuncPredName name;

    private ArgSortsOrFormula argSorts;

    @Nullable
    private Position position;

    @Nullable()
    public String docComment() {
        return docComment;
    }

    public TransformDecl setDocComment(@Nullable() String value) {
        docComment = value;
        return this;
    }

    @Nullable()
    public SortId returnSort() {
        return returnSort;
    }

    public TransformDecl setReturnSort(@Nullable() SortId value) {
        returnSort = value;
        return this;
    }

    public boolean isFormula() {
        return isFormula;
    }

    public TransformDecl setIsFormula(boolean value) {
        isFormula = value;
        return this;
    }

    public FuncPredName name() {
        return name;
    }

    public TransformDecl setName(FuncPredName value) {
        name = value;
        return this;
    }

    public ArgSortsOrFormula argSorts() {
        return argSorts;
    }

    public TransformDecl setArgSorts(ArgSortsOrFormula value) {
        argSorts = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public TransformDecl setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public TransformDecl(@Nullable String docComment, @Nullable SortId returnSort, boolean isFormula, FuncPredName name, ArgSortsOrFormula argSorts, @Nullable Position position) {
        this.docComment = docComment;
        this.returnSort = returnSort;
        this.isFormula = Objects.requireNonNull(isFormula);
        this.name = Objects.requireNonNull(name);
        this.argSorts = Objects.requireNonNull(argSorts);
        this.position = position;
    }

    public TransformDecl(boolean isFormula, FuncPredName name, ArgSortsOrFormula argSorts) {
        this.docComment = null;
        this.returnSort = null;
        this.isFormula = Objects.requireNonNull(isFormula);
        this.name = Objects.requireNonNull(name);
        this.argSorts = Objects.requireNonNull(argSorts);
        this.position = null;
    }

    public TransformDecl(TransformDecl other) {
        this(other.docComment, other.returnSort, other.isFormula, other.name, other.argSorts, other.position);
    }

    public final static class Builder {

        @Nullable()
        public String docComment;

        @Nullable()
        public SortId returnSort;

        @Nullable()
        public boolean isFormula;

        @Nullable()
        public FuncPredName name;

        @Nullable()
        public ArgSortsOrFormula argSorts;

        @Nullable()
        public Position position;

        public TransformDecl build() {
            return new TransformDecl(docComment, returnSort, isFormula, name, argSorts, position);
        }

        public Builder docComment(String docComment) {
            this.docComment = docComment;
            return this;
        }

        public Builder returnSort(SortId returnSort) {
            this.returnSort = returnSort;
            return this;
        }

        public Builder isFormula(boolean isFormula) {
            this.isFormula = isFormula;
            return this;
        }

        public Builder name(FuncPredName name) {
            this.name = name;
            return this;
        }

        public Builder argSorts(ArgSortsOrFormula argSorts) {
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
        b.returnSort = returnSort;
        b.isFormula = isFormula;
        b.name = name;
        b.argSorts = argSorts;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof TransformDecl that))
            return false;
        return Objects.equals(docComment, that.docComment) && Objects.equals(returnSort, that.returnSort) && Objects.equals(isFormula, that.isFormula) && Objects.equals(name, that.name) && Objects.equals(argSorts, that.argSorts) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "TransformDecl[docComment=%s, returnSort=%s, isFormula=%s, name=%s, argSorts=%s, position=%s]".formatted(docComment, returnSort, isFormula, name, argSorts, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(docComment, returnSort, isFormula, name, argSorts, position);
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
