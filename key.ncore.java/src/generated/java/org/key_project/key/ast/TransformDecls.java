package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class TransformDecls extends BaseAstNode {

    private List<TransformDecl> decls;

    @Nullable
    private Position position;

    public List<TransformDecl> decls() {
        return decls;
    }

    public TransformDecls setDecls(List<TransformDecl> value) {
        decls = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public TransformDecls setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public TransformDecls(List<TransformDecl> decls, @Nullable Position position) {
        this.decls = Objects.requireNonNull(decls);
        this.position = position;
    }

    public TransformDecls(List<TransformDecl> decls) {
        this.decls = Objects.requireNonNull(decls);
        this.position = null;
    }

    public TransformDecls(TransformDecls other) {
        this(other.decls, other.position);
    }

    public final static class Builder {

        @Nullable()
        public List<TransformDecl> decls;

        @Nullable()
        public Position position;

        public TransformDecls build() {
            return new TransformDecls(decls, position);
        }

        public Builder decls(List<TransformDecl> decls) {
            this.decls = decls;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder decls(TransformDecl decls) {
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
        if (!(o instanceof TransformDecls that))
            return false;
        return Objects.equals(decls, that.decls) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "TransformDecls[decls=%s, position=%s]".formatted(decls, position);
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
