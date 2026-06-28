package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class Term extends BaseAstNode {

    enum TermType {

        PARALLEL,
        ELEMENTARY_UPDATE,
        EQUIVALENCE,
        IMPLICATION,
        DISJUNCTION,
        CONJUNCTION,
        NEGATION,
        QUANTIFIER,
        MODALITY,
        EQUALITY,
        COMPARISON,
        WEAK_ARITH,
        STRONG_ARITH_1,
        STRONG_ARITH_2,
        UPDATE,
        SUBSTITUTION,
        CAST,
        UNARY_MINUS,
        BRACKET,
        IF_THEN_ELSE,
        IF_EX_THEN_ELSE,
        LOCATION,
        LOCSET,
        ACCESS,
        ABBREVIATION,
        LITERAL
    }

    private TermType type;

    private String operator;

    @Nullable
    private Term left;

    @Nullable
    private Term right;

    @Nullable
    private Term[] children;

    @Nullable
    private BoundVariables boundVariables;

    @Nullable
    private Label label;

    @Nullable
    private Position position;

    public TermType type() {
        return type;
    }

    public Term setType(TermType value) {
        type = value;
        return this;
    }

    public String operator() {
        return operator;
    }

    public Term setOperator(String value) {
        operator = value;
        return this;
    }

    @Nullable()
    public Term left() {
        return left;
    }

    public Term setLeft(@Nullable() Term value) {
        left = value;
        return this;
    }

    @Nullable()
    public Term right() {
        return right;
    }

    public Term setRight(@Nullable() Term value) {
        right = value;
        return this;
    }

    @Nullable()
    public Term[] children() {
        return children;
    }

    public Term setChildren(@Nullable() Term[] value) {
        children = value;
        return this;
    }

    @Nullable()
    public BoundVariables boundVariables() {
        return boundVariables;
    }

    public Term setBoundVariables(@Nullable() BoundVariables value) {
        boundVariables = value;
        return this;
    }

    @Nullable()
    public Label label() {
        return label;
    }

    public Term setLabel(@Nullable() Label value) {
        label = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public Term setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public Term(TermType type, String operator, @Nullable Term left, @Nullable Term right, @Nullable Term[] children, @Nullable BoundVariables boundVariables, @Nullable Label label, @Nullable Position position) {
        this.type = Objects.requireNonNull(type);
        this.operator = Objects.requireNonNull(operator);
        this.left = left;
        this.right = right;
        this.children = children;
        this.boundVariables = boundVariables;
        this.label = label;
        this.position = position;
    }

    public Term(TermType type, String operator) {
        this.type = Objects.requireNonNull(type);
        this.operator = Objects.requireNonNull(operator);
        this.left = null;
        this.right = null;
        this.children = null;
        this.boundVariables = null;
        this.label = null;
        this.position = null;
    }

    public Term(Term other) {
        this(other.type, other.operator, other.left, other.right, other.children, other.boundVariables, other.label, other.position);
    }

    public final static class Builder {

        @Nullable()
        public TermType type;

        @Nullable()
        public String operator;

        @Nullable()
        public Term left;

        @Nullable()
        public Term right;

        @Nullable()
        public Term[] children;

        @Nullable()
        public BoundVariables boundVariables;

        @Nullable()
        public Label label;

        @Nullable()
        public Position position;

        public Term build() {
            return new Term(type, operator, left, right, children, boundVariables, label, position);
        }

        public Builder type(TermType type) {
            this.type = type;
            return this;
        }

        public Builder operator(String operator) {
            this.operator = operator;
            return this;
        }

        public Builder left(Term left) {
            this.left = left;
            return this;
        }

        public Builder right(Term right) {
            this.right = right;
            return this;
        }

        public Builder children(Term[] children) {
            this.children = children;
            return this;
        }

        public Builder boundVariables(BoundVariables boundVariables) {
            this.boundVariables = boundVariables;
            return this;
        }

        public Builder label(Label label) {
            this.label = label;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.type = type;
        b.operator = operator;
        b.left = left;
        b.right = right;
        b.children = children;
        b.boundVariables = boundVariables;
        b.label = label;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Term that))
            return false;
        return Objects.equals(type, that.type) && Objects.equals(operator, that.operator) && Objects.equals(left, that.left) && Objects.equals(right, that.right) && Objects.equals(children, that.children) && Objects.equals(boundVariables, that.boundVariables) && Objects.equals(label, that.label) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "Term[type=%s, operator=%s, left=%s, right=%s, children=%s, boundVariables=%s, label=%s, position=%s]".formatted(type, operator, left, right, children, boundVariables, label, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(type, operator, left, right, children, boundVariables, label, position);
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
