package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class AddRules extends BaseAstNode {

    private List<String> ruleNames;

    @Nullable
    private Position position;

    public List<String> ruleNames() {
        return ruleNames;
    }

    public AddRules setRuleNames(List<String> value) {
        ruleNames = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public AddRules setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public AddRules(List<String> ruleNames, @Nullable Position position) {
        this.ruleNames = Objects.requireNonNull(ruleNames);
        this.position = position;
    }

    public AddRules(List<String> ruleNames) {
        this.ruleNames = Objects.requireNonNull(ruleNames);
        this.position = null;
    }

    public AddRules(AddRules other) {
        this(other.ruleNames, other.position);
    }

    public final static class Builder {

        @Nullable()
        public List<String> ruleNames;

        @Nullable()
        public Position position;

        public AddRules build() {
            return new AddRules(ruleNames, position);
        }

        public Builder ruleNames(List<String> ruleNames) {
            this.ruleNames = ruleNames;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder ruleNames(String ruleNames) {
            if (this.ruleNames == null)
                this.ruleNames = new ArrayList<>();
            this.ruleNames.add(ruleNames);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.ruleNames = ruleNames;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof AddRules that))
            return false;
        return Objects.equals(ruleNames, that.ruleNames) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "AddRules[ruleNames=%s, position=%s]".formatted(ruleNames, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(ruleNames, position);
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
