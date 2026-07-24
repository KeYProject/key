package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class LocsetTerm extends BaseAstNode {

    private List<Term> locations;

    @Nullable
    private Position position;

    public List<Term> locations() {
        return locations;
    }

    public LocsetTerm setLocations(List<Term> value) {
        locations = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public LocsetTerm setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public LocsetTerm(List<Term> locations, @Nullable Position position) {
        this.locations = Objects.requireNonNull(locations);
        this.position = position;
    }

    public LocsetTerm(List<Term> locations) {
        this.locations = Objects.requireNonNull(locations);
        this.position = null;
    }

    public LocsetTerm(LocsetTerm other) {
        this(other.locations, other.position);
    }

    public final static class Builder {

        @Nullable()
        public List<Term> locations;

        @Nullable()
        public Position position;

        public LocsetTerm build() {
            return new LocsetTerm(locations, position);
        }

        public Builder locations(List<Term> locations) {
            this.locations = locations;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder locations(Term locations) {
            if (this.locations == null)
                this.locations = new ArrayList<>();
            this.locations.add(locations);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.locations = locations;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof LocsetTerm that))
            return false;
        return Objects.equals(locations, that.locations) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "LocsetTerm[locations=%s, position=%s]".formatted(locations, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(locations, position);
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
