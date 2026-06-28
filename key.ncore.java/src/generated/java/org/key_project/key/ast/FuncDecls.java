package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class FuncDecls extends BaseAstNode {

    private List<FuncDecl> decls;

    @Nullable
    private Position position;

    public List<FuncDecl> decls() {
        return decls;
    }

    public FuncDecls setDecls(List<FuncDecl> value) {
        decls = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public FuncDecls setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public FuncDecls(List<FuncDecl> decls, @Nullable Position position) {
        this.decls = Objects.requireNonNull(decls);
        this.position = position;
    }

    public FuncDecls(List<FuncDecl> decls) {
        this.decls = Objects.requireNonNull(decls);
        this.position = null;
    }

    public FuncDecls(FuncDecls other) {
        this(other.decls, other.position);
    }

    public final static class Builder {

        @Nullable()
        public List<FuncDecl> decls;

        @Nullable()
        public Position position;

        public FuncDecls build() {
            return new FuncDecls(decls, position);
        }

        public Builder decls(List<FuncDecl> decls) {
            this.decls = decls;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder decls(FuncDecl decls) {
            if (this.decls == null)
                this.decls = new ArrayList<>();
            this.decls.add(decls);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.decls = decls;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof FuncDecls that))
            return false;
        return Objects.equals(decls, that.decls) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "FuncDecls[decls=%s, position=%s]".formatted(decls, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(decls, position);
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
