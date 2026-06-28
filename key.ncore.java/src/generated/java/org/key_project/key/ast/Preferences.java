package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class Preferences extends BaseAstNode {

    @Nullable
    private String stringValue;

    @Nullable
    private CValue cvalue;

    @Nullable
    private Position position;

    @Nullable()
    public String stringValue() {
        return stringValue;
    }

    public Preferences setStringValue(@Nullable() String value) {
        stringValue = value;
        return this;
    }

    @Nullable()
    public CValue cvalue() {
        return cvalue;
    }

    public Preferences setCvalue(@Nullable() CValue value) {
        cvalue = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public Preferences setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public Preferences(@Nullable String stringValue, @Nullable CValue cvalue, @Nullable Position position) {
        this.stringValue = stringValue;
        this.cvalue = cvalue;
        this.position = position;
    }

    public Preferences() {
        this.stringValue = null;
        this.cvalue = null;
        this.position = null;
    }

    public Preferences(Preferences other) {
        this(other.stringValue, other.cvalue, other.position);
    }

    public final static class Builder {

        @Nullable()
        public String stringValue;

        @Nullable()
        public CValue cvalue;

        @Nullable()
        public Position position;

        public Preferences build() {
            return new Preferences(stringValue, cvalue, position);
        }

        public Builder stringValue(String stringValue) {
            this.stringValue = stringValue;
            return this;
        }

        public Builder cvalue(CValue cvalue) {
            this.cvalue = cvalue;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.stringValue = stringValue;
        b.cvalue = cvalue;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Preferences that))
            return false;
        return Objects.equals(stringValue, that.stringValue) && Objects.equals(cvalue, that.cvalue) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "Preferences[stringValue=%s, cvalue=%s, position=%s]".formatted(stringValue, cvalue, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(stringValue, cvalue, position);
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
