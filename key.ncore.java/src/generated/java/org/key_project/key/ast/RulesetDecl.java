package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class RulesetDecl extends BaseAstNode {

    @Nullable
    private String docComment;

    private SimpleIdentDots name;

    private List<SimpleIdentDots> parentRules;

    @Nullable
    private Position position;

    @Nullable()
    public String docComment() {
        return docComment;
    }

    public RulesetDecl setDocComment(@Nullable() String value) {
        docComment = value;
        return this;
    }

    public SimpleIdentDots name() {
        return name;
    }

    public RulesetDecl setName(SimpleIdentDots value) {
        name = value;
        return this;
    }

    public List<SimpleIdentDots> parentRules() {
        return parentRules;
    }

    public RulesetDecl setParentRules(List<SimpleIdentDots> value) {
        parentRules = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public RulesetDecl setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public RulesetDecl(@Nullable String docComment, SimpleIdentDots name, List<SimpleIdentDots> parentRules, @Nullable Position position) {
        this.docComment = docComment;
        this.name = Objects.requireNonNull(name);
        this.parentRules = Objects.requireNonNull(parentRules);
        this.position = position;
    }

    public RulesetDecl(SimpleIdentDots name, List<SimpleIdentDots> parentRules) {
        this.docComment = null;
        this.name = Objects.requireNonNull(name);
        this.parentRules = Objects.requireNonNull(parentRules);
        this.position = null;
    }

    public RulesetDecl(RulesetDecl other) {
        this(other.docComment, other.name, other.parentRules, other.position);
    }

    public final static class Builder {

        @Nullable()
        public String docComment;

        @Nullable()
        public SimpleIdentDots name;

        @Nullable()
        public List<SimpleIdentDots> parentRules;

        @Nullable()
        public Position position;

        public RulesetDecl build() {
            return new RulesetDecl(docComment, name, parentRules, position);
        }

        public Builder docComment(String docComment) {
            this.docComment = docComment;
            return this;
        }

        public Builder name(SimpleIdentDots name) {
            this.name = name;
            return this;
        }

        public Builder parentRules(List<SimpleIdentDots> parentRules) {
            this.parentRules = parentRules;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder parentRules(SimpleIdentDots parentRules) {
            if (this.parentRules == null)
                this.parentRules = new ArrayList<>();
            this.parentRules.add(parentRules);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.docComment = docComment;
        b.name = name;
        b.parentRules = parentRules;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof RulesetDecl that))
            return false;
        return Objects.equals(docComment, that.docComment) && Objects.equals(name, that.name) && Objects.equals(parentRules, that.parentRules) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "RulesetDecl[docComment=%s, name=%s, parentRules=%s, position=%s]".formatted(docComment, name, parentRules, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(docComment, name, parentRules, position);
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
