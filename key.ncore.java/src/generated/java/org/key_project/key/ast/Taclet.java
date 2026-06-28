package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class Taclet extends BaseAstNode {

    @Nullable
    private String docComment;

    private boolean isLemma;

    private String name;

    @Nullable
    private OptionList options;

    private List<SchemaVarDecl> schemaVars;

    @Nullable
    private Seq assumes;

    @Nullable
    private TermOrSeq find;

    private List<String> findModifiers;

    private List<VarexpList> varConds;

    private GoalSpecs goalSpecs;

    private Modifiers modifiers;

    @Nullable
    private Position position;

    @Nullable()
    public String docComment() {
        return docComment;
    }

    public Taclet setDocComment(@Nullable() String value) {
        docComment = value;
        return this;
    }

    public boolean isLemma() {
        return isLemma;
    }

    public Taclet setIsLemma(boolean value) {
        isLemma = value;
        return this;
    }

    public String name() {
        return name;
    }

    public Taclet setName(String value) {
        name = value;
        return this;
    }

    @Nullable()
    public OptionList options() {
        return options;
    }

    public Taclet setOptions(@Nullable() OptionList value) {
        options = value;
        return this;
    }

    public List<SchemaVarDecl> schemaVars() {
        return schemaVars;
    }

    public Taclet setSchemaVars(List<SchemaVarDecl> value) {
        schemaVars = value;
        return this;
    }

    @Nullable()
    public Seq assumes() {
        return assumes;
    }

    public Taclet setAssumes(@Nullable() Seq value) {
        assumes = value;
        return this;
    }

    @Nullable()
    public TermOrSeq find() {
        return find;
    }

    public Taclet setFind(@Nullable() TermOrSeq value) {
        find = value;
        return this;
    }

    public List<String> findModifiers() {
        return findModifiers;
    }

    public Taclet setFindModifiers(List<String> value) {
        findModifiers = value;
        return this;
    }

    public List<VarexpList> varConds() {
        return varConds;
    }

    public Taclet setVarConds(List<VarexpList> value) {
        varConds = value;
        return this;
    }

    public GoalSpecs goalSpecs() {
        return goalSpecs;
    }

    public Taclet setGoalSpecs(GoalSpecs value) {
        goalSpecs = value;
        return this;
    }

    public Modifiers modifiers() {
        return modifiers;
    }

    public Taclet setModifiers(Modifiers value) {
        modifiers = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public Taclet setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public Taclet(@Nullable String docComment, boolean isLemma, String name, @Nullable OptionList options, List<SchemaVarDecl> schemaVars, @Nullable Seq assumes, @Nullable TermOrSeq find, List<String> findModifiers, List<VarexpList> varConds, GoalSpecs goalSpecs, Modifiers modifiers, @Nullable Position position) {
        this.docComment = docComment;
        this.isLemma = Objects.requireNonNull(isLemma);
        this.name = Objects.requireNonNull(name);
        this.options = options;
        this.schemaVars = Objects.requireNonNull(schemaVars);
        this.assumes = assumes;
        this.find = find;
        this.findModifiers = Objects.requireNonNull(findModifiers);
        this.varConds = Objects.requireNonNull(varConds);
        this.goalSpecs = Objects.requireNonNull(goalSpecs);
        this.modifiers = Objects.requireNonNull(modifiers);
        this.position = position;
    }

    public Taclet(boolean isLemma, String name, List<SchemaVarDecl> schemaVars, List<String> findModifiers, List<VarexpList> varConds, GoalSpecs goalSpecs, Modifiers modifiers) {
        this.docComment = null;
        this.isLemma = Objects.requireNonNull(isLemma);
        this.name = Objects.requireNonNull(name);
        this.options = null;
        this.schemaVars = Objects.requireNonNull(schemaVars);
        this.assumes = null;
        this.find = null;
        this.findModifiers = Objects.requireNonNull(findModifiers);
        this.varConds = Objects.requireNonNull(varConds);
        this.goalSpecs = Objects.requireNonNull(goalSpecs);
        this.modifiers = Objects.requireNonNull(modifiers);
        this.position = null;
    }

    public Taclet(Taclet other) {
        this(other.docComment, other.isLemma, other.name, other.options, other.schemaVars, other.assumes, other.find, other.findModifiers, other.varConds, other.goalSpecs, other.modifiers, other.position);
    }

    public final static class Builder {

        @Nullable()
        public String docComment;

        @Nullable()
        public boolean isLemma;

        @Nullable()
        public String name;

        @Nullable()
        public OptionList options;

        @Nullable()
        public List<SchemaVarDecl> schemaVars;

        @Nullable()
        public Seq assumes;

        @Nullable()
        public TermOrSeq find;

        @Nullable()
        public List<String> findModifiers;

        @Nullable()
        public List<VarexpList> varConds;

        @Nullable()
        public GoalSpecs goalSpecs;

        @Nullable()
        public Modifiers modifiers;

        @Nullable()
        public Position position;

        public Taclet build() {
            return new Taclet(docComment, isLemma, name, options, schemaVars, assumes, find, findModifiers, varConds, goalSpecs, modifiers, position);
        }

        public Builder docComment(String docComment) {
            this.docComment = docComment;
            return this;
        }

        public Builder isLemma(boolean isLemma) {
            this.isLemma = isLemma;
            return this;
        }

        public Builder name(String name) {
            this.name = name;
            return this;
        }

        public Builder options(OptionList options) {
            this.options = options;
            return this;
        }

        public Builder schemaVars(List<SchemaVarDecl> schemaVars) {
            this.schemaVars = schemaVars;
            return this;
        }

        public Builder assumes(Seq assumes) {
            this.assumes = assumes;
            return this;
        }

        public Builder find(TermOrSeq find) {
            this.find = find;
            return this;
        }

        public Builder findModifiers(List<String> findModifiers) {
            this.findModifiers = findModifiers;
            return this;
        }

        public Builder varConds(List<VarexpList> varConds) {
            this.varConds = varConds;
            return this;
        }

        public Builder goalSpecs(GoalSpecs goalSpecs) {
            this.goalSpecs = goalSpecs;
            return this;
        }

        public Builder modifiers(Modifiers modifiers) {
            this.modifiers = modifiers;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder schemaVars(SchemaVarDecl schemaVars) {
            if (this.schemaVars == null)
                this.schemaVars = new ArrayList<>();
            this.schemaVars.add(schemaVars);
            return this;
        }

        public Builder findModifiers(String findModifiers) {
            if (this.findModifiers == null)
                this.findModifiers = new ArrayList<>();
            this.findModifiers.add(findModifiers);
            return this;
        }

        public Builder varConds(VarexpList varConds) {
            if (this.varConds == null)
                this.varConds = new ArrayList<>();
            this.varConds.add(varConds);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.docComment = docComment;
        b.isLemma = isLemma;
        b.name = name;
        b.options = options;
        b.schemaVars = schemaVars;
        b.assumes = assumes;
        b.find = find;
        b.findModifiers = findModifiers;
        b.varConds = varConds;
        b.goalSpecs = goalSpecs;
        b.modifiers = modifiers;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Taclet that))
            return false;
        return Objects.equals(docComment, that.docComment) && Objects.equals(isLemma, that.isLemma) && Objects.equals(name, that.name) && Objects.equals(options, that.options) && Objects.equals(schemaVars, that.schemaVars) && Objects.equals(assumes, that.assumes) && Objects.equals(find, that.find) && Objects.equals(findModifiers, that.findModifiers) && Objects.equals(varConds, that.varConds) && Objects.equals(goalSpecs, that.goalSpecs) && Objects.equals(modifiers, that.modifiers) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "Taclet[docComment=%s, isLemma=%s, name=%s, options=%s, schemaVars=%s, assumes=%s, find=%s, findModifiers=%s, varConds=%s, goalSpecs=%s, modifiers=%s, position=%s]".formatted(docComment, isLemma, name, options, schemaVars, assumes, find, findModifiers, varConds, goalSpecs, modifiers, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(docComment, isLemma, name, options, schemaVars, assumes, find, findModifiers, varConds, goalSpecs, modifiers, position);
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
