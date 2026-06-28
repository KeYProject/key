package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class GoalSpecs extends BaseAstNode {

    private List<GoalSpec> specs;

    @Nullable
    private Position position;

    public List<GoalSpec> specs() {
        return specs;
    }

    public GoalSpecs setSpecs(List<GoalSpec> value) {
        specs = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public GoalSpecs setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public GoalSpecs(List<GoalSpec> specs, @Nullable Position position) {
        this.specs = Objects.requireNonNull(specs);
        this.position = position;
    }

    public GoalSpecs(List<GoalSpec> specs) {
        this.specs = Objects.requireNonNull(specs);
        this.position = null;
    }

    public GoalSpecs(GoalSpecs other) {
        this(other.specs, other.position);
    }

    public final static class Builder {

        @Nullable()
        public List<GoalSpec> specs;

        @Nullable()
        public Position position;

        public GoalSpecs build() {
            return new GoalSpecs(specs, position);
        }

        public Builder specs(List<GoalSpec> specs) {
            this.specs = specs;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder specs(GoalSpec specs) {
            if (this.specs == null)
                this.specs = new ArrayList<>();
            this.specs.add(specs);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.specs = specs;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof GoalSpecs that))
            return false;
        return Objects.equals(specs, that.specs) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "GoalSpecs[specs=%s, position=%s]".formatted(specs, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(specs, position);
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
