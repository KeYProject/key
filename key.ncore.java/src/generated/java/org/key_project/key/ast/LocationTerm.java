package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class LocationTerm extends BaseAstNode {

    private String baseName;

    @Nullable
    private Term qualifier;

    private java.util.List<String> fieldChain;

    private java.util.List<Term> arrayIndices;

    @Nullable
    private Position position;

    public String baseName() {
        return baseName;
    }

    public LocationTerm setBaseName(String value) {
        baseName = value;
        return this;
    }

    @Nullable()
    public Term qualifier() {
        return qualifier;
    }

    public LocationTerm setQualifier(@Nullable() Term value) {
        qualifier = value;
        return this;
    }

    public java.util.List<String> fieldChain() {
        return fieldChain;
    }

    public LocationTerm setFieldChain(java.util.List<String> value) {
        fieldChain = value;
        return this;
    }

    public java.util.List<Term> arrayIndices() {
        return arrayIndices;
    }

    public LocationTerm setArrayIndices(java.util.List<Term> value) {
        arrayIndices = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public LocationTerm setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public LocationTerm(String baseName, @Nullable Term qualifier, java.util.List<String> fieldChain, java.util.List<Term> arrayIndices, @Nullable Position position) {
        this.baseName = Objects.requireNonNull(baseName);
        this.qualifier = qualifier;
        this.fieldChain = Objects.requireNonNull(fieldChain);
        this.arrayIndices = Objects.requireNonNull(arrayIndices);
        this.position = position;
    }

    public LocationTerm(String baseName, java.util.List<String> fieldChain, java.util.List<Term> arrayIndices) {
        this.baseName = Objects.requireNonNull(baseName);
        this.qualifier = null;
        this.fieldChain = Objects.requireNonNull(fieldChain);
        this.arrayIndices = Objects.requireNonNull(arrayIndices);
        this.position = null;
    }

    public LocationTerm(LocationTerm other) {
        this(other.baseName, other.qualifier, other.fieldChain, other.arrayIndices, other.position);
    }

    public final static class Builder {

        @Nullable()
        public String baseName;

        @Nullable()
        public Term qualifier;

        @Nullable()
        public java.util.List<String> fieldChain;

        @Nullable()
        public java.util.List<Term> arrayIndices;

        @Nullable()
        public Position position;

        public LocationTerm build() {
            return new LocationTerm(baseName, qualifier, fieldChain, arrayIndices, position);
        }

        public Builder baseName(String baseName) {
            this.baseName = baseName;
            return this;
        }

        public Builder qualifier(Term qualifier) {
            this.qualifier = qualifier;
            return this;
        }

        public Builder fieldChain(java.util.List<String> fieldChain) {
            this.fieldChain = fieldChain;
            return this;
        }

        public Builder arrayIndices(java.util.List<Term> arrayIndices) {
            this.arrayIndices = arrayIndices;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder fieldChain(String fieldChain) {
            if (this.fieldChain == null)
                this.fieldChain = new ArrayList<>();
            this.fieldChain.add(fieldChain);
            return this;
        }

        public Builder arrayIndices(Term arrayIndices) {
            if (this.arrayIndices == null)
                this.arrayIndices = new ArrayList<>();
            this.arrayIndices.add(arrayIndices);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.baseName = baseName;
        b.qualifier = qualifier;
        b.fieldChain = fieldChain;
        b.arrayIndices = arrayIndices;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof LocationTerm that))
            return false;
        return Objects.equals(baseName, that.baseName) && Objects.equals(qualifier, that.qualifier) && Objects.equals(fieldChain, that.fieldChain) && Objects.equals(arrayIndices, that.arrayIndices) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "LocationTerm[baseName=%s, qualifier=%s, fieldChain=%s, arrayIndices=%s, position=%s]".formatted(baseName, qualifier, fieldChain, arrayIndices, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(baseName, qualifier, fieldChain, arrayIndices, position);
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
