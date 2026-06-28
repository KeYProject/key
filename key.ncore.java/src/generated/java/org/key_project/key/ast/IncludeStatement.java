package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class IncludeStatement extends BaseAstNode {

    private boolean isLdt;

    private List<OneInclude> includes;

    @Nullable
    private Position position;

    public boolean isLdt() {
        return isLdt;
    }

    public IncludeStatement setIsLdt(boolean value) {
        isLdt = value;
        return this;
    }

    public List<OneInclude> includes() {
        return includes;
    }

    public IncludeStatement setIncludes(List<OneInclude> value) {
        includes = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public IncludeStatement setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public IncludeStatement(boolean isLdt, List<OneInclude> includes, @Nullable Position position) {
        this.isLdt = Objects.requireNonNull(isLdt);
        this.includes = Objects.requireNonNull(includes);
        this.position = position;
    }

    public IncludeStatement(boolean isLdt, List<OneInclude> includes) {
        this.isLdt = Objects.requireNonNull(isLdt);
        this.includes = Objects.requireNonNull(includes);
        this.position = null;
    }

    public IncludeStatement(IncludeStatement other) {
        this(other.isLdt, other.includes, other.position);
    }

    public final static class Builder {

        @Nullable()
        public boolean isLdt;

        @Nullable()
        public List<OneInclude> includes;

        @Nullable()
        public Position position;

        public IncludeStatement build() {
            return new IncludeStatement(isLdt, includes, position);
        }

        public Builder isLdt(boolean isLdt) {
            this.isLdt = isLdt;
            return this;
        }

        public Builder includes(List<OneInclude> includes) {
            this.includes = includes;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder includes(OneInclude includes) {
            if (this.includes == null)
                this.includes = new ArrayList<>();
            this.includes.add(includes);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.isLdt = isLdt;
        b.includes = includes;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof IncludeStatement that))
            return false;
        return Objects.equals(isLdt, that.isLdt) && Objects.equals(includes, that.includes) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "IncludeStatement[isLdt=%s, includes=%s, position=%s]".formatted(isLdt, includes, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(isLdt, includes, position);
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
