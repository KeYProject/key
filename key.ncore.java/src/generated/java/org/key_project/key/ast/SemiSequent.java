package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class SemiSequent extends BaseAstNode {

    private Seq antecedent;

    private Seq succulent;

    @Nullable
    private Position position;

    public Seq antecedent() {
        return antecedent;
    }

    public SemiSequent setAntecedent(Seq value) {
        antecedent = value;
        return this;
    }

    public Seq succulent() {
        return succulent;
    }

    public SemiSequent setSucculent(Seq value) {
        succulent = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public SemiSequent setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public SemiSequent(Seq antecedent, Seq succulent, @Nullable Position position) {
        this.antecedent = Objects.requireNonNull(antecedent);
        this.succulent = Objects.requireNonNull(succulent);
        this.position = position;
    }

    public SemiSequent(Seq antecedent, Seq succulent) {
        this.antecedent = Objects.requireNonNull(antecedent);
        this.succulent = Objects.requireNonNull(succulent);
        this.position = null;
    }

    public SemiSequent(SemiSequent other) {
        this(other.antecedent, other.succulent, other.position);
    }

    public final static class Builder {

        @Nullable()
        public Seq antecedent;

        @Nullable()
        public Seq succulent;

        @Nullable()
        public Position position;

        public SemiSequent build() {
            return new SemiSequent(antecedent, succulent, position);
        }

        public Builder antecedent(Seq antecedent) {
            this.antecedent = antecedent;
            return this;
        }

        public Builder succulent(Seq succulent) {
            this.succulent = succulent;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.antecedent = antecedent;
        b.succulent = succulent;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof SemiSequent that))
            return false;
        return Objects.equals(antecedent, that.antecedent) && Objects.equals(succulent, that.succulent) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "SemiSequent[antecedent=%s, succulent=%s, position=%s]".formatted(antecedent, succulent, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(antecedent, succulent, position);
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
