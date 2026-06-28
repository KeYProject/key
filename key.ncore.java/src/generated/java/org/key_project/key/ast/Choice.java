package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class Choice extends BaseAstNode {

    private List<String> docComments;

    private String category;

    @Nullable
    private List<String> optionDecls;

    @Nullable
    private Position position;

    public List<String> docComments() {
        return docComments;
    }

    public Choice setDocComments(List<String> value) {
        docComments = value;
        return this;
    }

    public String category() {
        return category;
    }

    public Choice setCategory(String value) {
        category = value;
        return this;
    }

    @Nullable()
    public List<String> optionDecls() {
        return optionDecls;
    }

    public Choice setOptionDecls(@Nullable() List<String> value) {
        optionDecls = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public Choice setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public Choice(List<String> docComments, String category, @Nullable List<String> optionDecls, @Nullable Position position) {
        this.docComments = Objects.requireNonNull(docComments);
        this.category = Objects.requireNonNull(category);
        this.optionDecls = optionDecls;
        this.position = position;
    }

    public Choice(List<String> docComments, String category) {
        this.docComments = Objects.requireNonNull(docComments);
        this.category = Objects.requireNonNull(category);
        this.optionDecls = null;
        this.position = null;
    }

    public Choice(Choice other) {
        this(other.docComments, other.category, other.optionDecls, other.position);
    }

    public final static class Builder {

        @Nullable()
        public List<String> docComments;

        @Nullable()
        public String category;

        @Nullable()
        public List<String> optionDecls;

        @Nullable()
        public Position position;

        public Choice build() {
            return new Choice(docComments, category, optionDecls, position);
        }

        public Builder docComments(List<String> docComments) {
            this.docComments = docComments;
            return this;
        }

        public Builder category(String category) {
            this.category = category;
            return this;
        }

        public Builder optionDecls(List<String> optionDecls) {
            this.optionDecls = optionDecls;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder docComments(String docComments) {
            if (this.docComments == null)
                this.docComments = new ArrayList<>();
            this.docComments.add(docComments);
            return this;
        }

        public Builder optionDecls(String optionDecls) {
            if (this.optionDecls == null)
                this.optionDecls = new ArrayList<>();
            this.optionDecls.add(optionDecls);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.docComments = docComments;
        b.category = category;
        b.optionDecls = optionDecls;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Choice that))
            return false;
        return Objects.equals(docComments, that.docComments) && Objects.equals(category, that.category) && Objects.equals(optionDecls, that.optionDecls) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "Choice[docComments=%s, category=%s, optionDecls=%s, position=%s]".formatted(docComments, category, optionDecls, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(docComments, category, optionDecls, position);
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
