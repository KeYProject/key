package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class File extends BaseAstNode {

    private List<String> docComments;

    @Nullable
    private Profile profile;

    @Nullable
    private Preferences preferences;

    private DeclList decls;

    @Nullable
    private Problem problem;

    @Nullable
    private Proof proof;

    @Nullable
    private Position position;

    public List<String> docComments() {
        return docComments;
    }

    public File setDocComments(List<String> value) {
        docComments = value;
        return this;
    }

    @Nullable()
    public Profile profile() {
        return profile;
    }

    public File setProfile(@Nullable() Profile value) {
        profile = value;
        return this;
    }

    @Nullable()
    public Preferences preferences() {
        return preferences;
    }

    public File setPreferences(@Nullable() Preferences value) {
        preferences = value;
        return this;
    }

    public DeclList decls() {
        return decls;
    }

    public File setDecls(DeclList value) {
        decls = value;
        return this;
    }

    @Nullable()
    public Problem problem() {
        return problem;
    }

    public File setProblem(@Nullable() Problem value) {
        problem = value;
        return this;
    }

    @Nullable()
    public Proof proof() {
        return proof;
    }

    public File setProof(@Nullable() Proof value) {
        proof = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public File setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public File(List<String> docComments, @Nullable Profile profile, @Nullable Preferences preferences, DeclList decls, @Nullable Problem problem, @Nullable Proof proof, @Nullable Position position) {
        this.docComments = Objects.requireNonNull(docComments);
        this.profile = profile;
        this.preferences = preferences;
        this.decls = Objects.requireNonNull(decls);
        this.problem = problem;
        this.proof = proof;
        this.position = position;
    }

    public File(List<String> docComments, DeclList decls) {
        this.docComments = Objects.requireNonNull(docComments);
        this.profile = null;
        this.preferences = null;
        this.decls = Objects.requireNonNull(decls);
        this.problem = null;
        this.proof = null;
        this.position = null;
    }

    public File(File other) {
        this(other.docComments, other.profile, other.preferences, other.decls, other.problem, other.proof, other.position);
    }

    public final static class Builder {

        @Nullable()
        public List<String> docComments;

        @Nullable()
        public Profile profile;

        @Nullable()
        public Preferences preferences;

        @Nullable()
        public DeclList decls;

        @Nullable()
        public Problem problem;

        @Nullable()
        public Proof proof;

        @Nullable()
        public Position position;

        public File build() {
            return new File(docComments, profile, preferences, decls, problem, proof, position);
        }

        public Builder docComments(List<String> docComments) {
            this.docComments = docComments;
            return this;
        }

        public Builder profile(Profile profile) {
            this.profile = profile;
            return this;
        }

        public Builder preferences(Preferences preferences) {
            this.preferences = preferences;
            return this;
        }

        public Builder decls(DeclList decls) {
            this.decls = decls;
            return this;
        }

        public Builder problem(Problem problem) {
            this.problem = problem;
            return this;
        }

        public Builder proof(Proof proof) {
            this.proof = proof;
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
    }

    public Builder builder() {
        Builder b = new Builder();
        b.docComments = docComments;
        b.profile = profile;
        b.preferences = preferences;
        b.decls = decls;
        b.problem = problem;
        b.proof = proof;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof File that))
            return false;
        return Objects.equals(docComments, that.docComments) && Objects.equals(profile, that.profile) && Objects.equals(preferences, that.preferences) && Objects.equals(decls, that.decls) && Objects.equals(problem, that.problem) && Objects.equals(proof, that.proof) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "File[docComments=%s, profile=%s, preferences=%s, decls=%s, problem=%s, proof=%s, position=%s]".formatted(docComments, profile, preferences, decls, problem, proof, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(docComments, profile, preferences, decls, problem, proof, position);
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
