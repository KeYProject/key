package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class SortDecls extends BaseAstNode {

    private List<OneSortDecl> sortDecls;

    @Nullable
    private Position position;

    public List<OneSortDecl> sortDecls() {
        return sortDecls;
    }

    public SortDecls setSortDecls(List<OneSortDecl> value) {
        sortDecls = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public SortDecls setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public SortDecls(List<OneSortDecl> sortDecls, @Nullable Position position) {
        this.sortDecls = Objects.requireNonNull(sortDecls);
        this.position = position;
    }

    public SortDecls(List<OneSortDecl> sortDecls) {
        this.sortDecls = Objects.requireNonNull(sortDecls);
        this.position = null;
    }

    public SortDecls(SortDecls other) {
        this(other.sortDecls, other.position);
    }

    public final static class Builder {

        @Nullable()
        public List<OneSortDecl> sortDecls;

        @Nullable()
        public Position position;

        public SortDecls build() {
            return new SortDecls(sortDecls, position);
        }

        public Builder sortDecls(List<OneSortDecl> sortDecls) {
            this.sortDecls = sortDecls;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder sortDecls(OneSortDecl sortDecls) {
            if (this.sortDecls == null)
                this.sortDecls = new ArrayList<>();
            this.sortDecls.add(sortDecls);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.sortDecls = sortDecls;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof SortDecls that))
            return false;
        return Objects.equals(sortDecls, that.sortDecls) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "SortDecls[sortDecls=%s, position=%s]".formatted(sortDecls, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(sortDecls, position);
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
