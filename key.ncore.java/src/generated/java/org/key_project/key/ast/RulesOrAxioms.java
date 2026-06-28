package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class RulesOrAxioms extends BaseAstNode {

    @Nullable
    private String name;

    @Nullable
    private Term condition;

    private boolean isAxiom;

    private Formula formula;

    @Nullable
    private Formula whenCondition;

    private List<String> rulesetNames;

    @Nullable
    private Position position;

    @Nullable()
    public String name() {
        return name;
    }

    public RulesOrAxioms setName(@Nullable() String value) {
        name = value;
        return this;
    }

    @Nullable()
    public Term condition() {
        return condition;
    }

    public RulesOrAxioms setCondition(@Nullable() Term value) {
        condition = value;
        return this;
    }

    public boolean isAxiom() {
        return isAxiom;
    }

    public RulesOrAxioms setIsAxiom(boolean value) {
        isAxiom = value;
        return this;
    }

    public Formula formula() {
        return formula;
    }

    public RulesOrAxioms setFormula(Formula value) {
        formula = value;
        return this;
    }

    @Nullable()
    public Formula whenCondition() {
        return whenCondition;
    }

    public RulesOrAxioms setWhenCondition(@Nullable() Formula value) {
        whenCondition = value;
        return this;
    }

    public List<String> rulesetNames() {
        return rulesetNames;
    }

    public RulesOrAxioms setRulesetNames(List<String> value) {
        rulesetNames = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public RulesOrAxioms setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public RulesOrAxioms(@Nullable String name, @Nullable Term condition, boolean isAxiom, Formula formula, @Nullable Formula whenCondition, List<String> rulesetNames, @Nullable Position position) {
        this.name = name;
        this.condition = condition;
        this.isAxiom = Objects.requireNonNull(isAxiom);
        this.formula = Objects.requireNonNull(formula);
        this.whenCondition = whenCondition;
        this.rulesetNames = Objects.requireNonNull(rulesetNames);
        this.position = position;
    }

    public RulesOrAxioms(boolean isAxiom, Formula formula, List<String> rulesetNames) {
        this.name = null;
        this.condition = null;
        this.isAxiom = Objects.requireNonNull(isAxiom);
        this.formula = Objects.requireNonNull(formula);
        this.whenCondition = null;
        this.rulesetNames = Objects.requireNonNull(rulesetNames);
        this.position = null;
    }

    public RulesOrAxioms(RulesOrAxioms other) {
        this(other.name, other.condition, other.isAxiom, other.formula, other.whenCondition, other.rulesetNames, other.position);
    }

    public final static class Builder {

        @Nullable()
        public String name;

        @Nullable()
        public Term condition;

        @Nullable()
        public boolean isAxiom;

        @Nullable()
        public Formula formula;

        @Nullable()
        public Formula whenCondition;

        @Nullable()
        public List<String> rulesetNames;

        @Nullable()
        public Position position;

        public RulesOrAxioms build() {
            return new RulesOrAxioms(name, condition, isAxiom, formula, whenCondition, rulesetNames, position);
        }

        public Builder name(String name) {
            this.name = name;
            return this;
        }

        public Builder condition(Term condition) {
            this.condition = condition;
            return this;
        }

        public Builder isAxiom(boolean isAxiom) {
            this.isAxiom = isAxiom;
            return this;
        }

        public Builder formula(Formula formula) {
            this.formula = formula;
            return this;
        }

        public Builder whenCondition(Formula whenCondition) {
            this.whenCondition = whenCondition;
            return this;
        }

        public Builder rulesetNames(List<String> rulesetNames) {
            this.rulesetNames = rulesetNames;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder rulesetNames(String rulesetNames) {
            if (this.rulesetNames == null)
                this.rulesetNames = new ArrayList<>();
            this.rulesetNames.add(rulesetNames);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.name = name;
        b.condition = condition;
        b.isAxiom = isAxiom;
        b.formula = formula;
        b.whenCondition = whenCondition;
        b.rulesetNames = rulesetNames;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof RulesOrAxioms that))
            return false;
        return Objects.equals(name, that.name) && Objects.equals(condition, that.condition) && Objects.equals(isAxiom, that.isAxiom) && Objects.equals(formula, that.formula) && Objects.equals(whenCondition, that.whenCondition) && Objects.equals(rulesetNames, that.rulesetNames) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "RulesOrAxioms[name=%s, condition=%s, isAxiom=%s, formula=%s, whenCondition=%s, rulesetNames=%s, position=%s]".formatted(name, condition, isAxiom, formula, whenCondition, rulesetNames, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(name, condition, isAxiom, formula, whenCondition, rulesetNames, position);
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
