package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class ModalityTerm extends BaseAstNode {

    private boolean isBox;

    private Term program;

    private Term body;

    @Nullable
    private Position position;

    public boolean isBox() {
        return isBox;
    }

    public ModalityTerm setIsBox(boolean value) {
        isBox = value;
        return this;
    }

    public Term program() {
        return program;
    }

    public ModalityTerm setProgram(Term value) {
        program = value;
        return this;
    }

    public Term body() {
        return body;
    }

    public ModalityTerm setBody(Term value) {
        body = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public ModalityTerm setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public ModalityTerm(boolean isBox, Term program, Term body, @Nullable Position position) {
        this.isBox = Objects.requireNonNull(isBox);
        this.program = Objects.requireNonNull(program);
        this.body = Objects.requireNonNull(body);
        this.position = position;
    }

    public ModalityTerm(boolean isBox, Term program, Term body) {
        this.isBox = Objects.requireNonNull(isBox);
        this.program = Objects.requireNonNull(program);
        this.body = Objects.requireNonNull(body);
        this.position = null;
    }

    public ModalityTerm(ModalityTerm other) {
        this(other.isBox, other.program, other.body, other.position);
    }

    public final static class Builder {

        @Nullable()
        public boolean isBox;

        @Nullable()
        public Term program;

        @Nullable()
        public Term body;

        @Nullable()
        public Position position;

        public ModalityTerm build() {
            return new ModalityTerm(isBox, program, body, position);
        }

        public Builder isBox(boolean isBox) {
            this.isBox = isBox;
            return this;
        }

        public Builder program(Term program) {
            this.program = program;
            return this;
        }

        public Builder body(Term body) {
            this.body = body;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.isBox = isBox;
        b.program = program;
        b.body = body;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof ModalityTerm that))
            return false;
        return Objects.equals(isBox, that.isBox) && Objects.equals(program, that.program) && Objects.equals(body, that.body) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "ModalityTerm[isBox=%s, program=%s, body=%s, position=%s]".formatted(isBox, program, body, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(isBox, program, body, position);
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
