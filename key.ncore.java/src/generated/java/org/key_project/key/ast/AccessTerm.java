package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class AccessTerm extends BaseAstNode {

    private LocationTerm location;

    @Nullable
    private Position position;

    public LocationTerm location() {
        return location;
    }

    public AccessTerm setLocation(LocationTerm value) {
        location = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public AccessTerm setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public AccessTerm(LocationTerm location, @Nullable Position position) {
        this.location = Objects.requireNonNull(location);
        this.position = position;
    }

    public AccessTerm(LocationTerm location) {
        this.location = Objects.requireNonNull(location);
        this.position = null;
    }

    public AccessTerm(AccessTerm other) {
        this(other.location, other.position);
    }

    public final static class Builder {

        @Nullable()
        public LocationTerm location;

        @Nullable()
        public Position position;

        public AccessTerm build() {
            return new AccessTerm(location, position);
        }

        public Builder location(LocationTerm location) {
            this.location = location;
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
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof AccessTerm that))
            return false;
        return Objects.equals(location, that.location) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "AccessTerm[location=%s, position=%s]".formatted(location, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(location, position);
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
