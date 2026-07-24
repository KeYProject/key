package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class ConfigurationFile extends BaseAstNode {

    private List<CKV> entries;

    @Nullable
    private Position position;

    public List<CKV> entries() {
        return entries;
    }

    public ConfigurationFile setEntries(List<CKV> value) {
        entries = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public ConfigurationFile setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public ConfigurationFile(List<CKV> entries, @Nullable Position position) {
        this.entries = Objects.requireNonNull(entries);
        this.position = position;
    }

    public ConfigurationFile(List<CKV> entries) {
        this.entries = Objects.requireNonNull(entries);
        this.position = null;
    }

    public ConfigurationFile(ConfigurationFile other) {
        this(other.entries, other.position);
    }

    public final static class Builder {

        @Nullable()
        public List<CKV> entries;

        @Nullable()
        public Position position;

        public ConfigurationFile build() {
            return new ConfigurationFile(entries, position);
        }

        public Builder entries(List<CKV> entries) {
            this.entries = entries;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder entries(CKV entries) {
            if (this.entries == null)
                this.entries = new ArrayList<>();
            this.entries.add(entries);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.entries = entries;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof ConfigurationFile that))
            return false;
        return Objects.equals(entries, that.entries) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "ConfigurationFile[entries=%s, position=%s]".formatted(entries, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(entries, position);
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
