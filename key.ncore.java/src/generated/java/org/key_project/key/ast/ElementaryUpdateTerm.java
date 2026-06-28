package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class ElementaryUpdateTerm extends BaseAstNode {

    private LocationTerm location;

    private Term value;

    @Nullable
    private Position position;

    public LocationTerm location() {
        return location;
    }

    public ElementaryUpdateTerm setLocation(LocationTerm value) {
        location = value;
        return this;
    }

    public Term value() {
        return value;
    }

    public ElementaryUpdateTerm setValue(Term value) {
        value = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public ElementaryUpdateTerm setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public ElementaryUpdateTerm(LocationTerm location, Term value, @Nullable Position position) {
        this.location = Objects.requireNonNull(location);
        this.value = Objects.requireNonNull(value);
        this.position = position;
    }

    public ElementaryUpdateTerm(LocationTerm location, Term value) {
        this.location = Objects.requireNonNull(location);
        this.value = Objects.requireNonNull(value);
        this.position = null;
    }

    public ElementaryUpdateTerm(ElementaryUpdateTerm other) {
        this(other.location, other.value, other.position);
    }

    public final static class Builder {

        @Nullable()
        public LocationTerm location;

        @Nullable()
        public Term value;

        @Nullable()
        public Position position;

        public ElementaryUpdateTerm build() {
            return new ElementaryUpdateTerm(location, value, position);
        }

        public Builder location(LocationTerm location) {
            this.location = location;
            return this;
        }

        public Builder value(Term value) {
            this.value = value;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.location = location;
        b.value = value;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof ElementaryUpdateTerm that))
            return false;
        return Objects.equals(location, that.location) && Objects.equals(value, that.value) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "ElementaryUpdateTerm[location=%s, value=%s, position=%s]".formatted(location, value, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(location, value, position);
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
