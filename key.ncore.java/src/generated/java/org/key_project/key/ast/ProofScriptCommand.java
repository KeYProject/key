package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class ProofScriptCommand extends BaseAstNode {

    private String name;

    private java.util.List<String> arguments;

    @Nullable
    private Position position;

    public String name() {
        return name;
    }

    public ProofScriptCommand setName(String value) {
        name = value;
        return this;
    }

    public java.util.List<String> arguments() {
        return arguments;
    }

    public ProofScriptCommand setArguments(java.util.List<String> value) {
        arguments = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public ProofScriptCommand setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public ProofScriptCommand(String name, java.util.List<String> arguments, @Nullable Position position) {
        this.name = Objects.requireNonNull(name);
        this.arguments = Objects.requireNonNull(arguments);
        this.position = position;
    }

    public ProofScriptCommand(String name, java.util.List<String> arguments) {
        this.name = Objects.requireNonNull(name);
        this.arguments = Objects.requireNonNull(arguments);
        this.position = null;
    }

    public ProofScriptCommand(ProofScriptCommand other) {
        this(other.name, other.arguments, other.position);
    }

    public final static class Builder {

        @Nullable()
        public String name;

        @Nullable()
        public java.util.List<String> arguments;

        @Nullable()
        public Position position;

        public ProofScriptCommand build() {
            return new ProofScriptCommand(name, arguments, position);
        }

        public Builder name(String name) {
            this.name = name;
            return this;
        }

        public Builder arguments(java.util.List<String> arguments) {
            this.arguments = arguments;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder arguments(String arguments) {
            if (this.arguments == null)
                this.arguments = new ArrayList<>();
            this.arguments.add(arguments);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.name = name;
        b.arguments = arguments;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof ProofScriptCommand that))
            return false;
        return Objects.equals(name, that.name) && Objects.equals(arguments, that.arguments) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "ProofScriptCommand[name=%s, arguments=%s, position=%s]".formatted(name, arguments, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(name, arguments, position);
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
