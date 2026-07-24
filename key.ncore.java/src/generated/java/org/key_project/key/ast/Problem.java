package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class Problem extends BaseAstNode {

    @Nullable
    private Term termOrSeq;

    @Nullable
    private String chooseContract;

    @Nullable
    private String proofObligation;

    @Nullable
    private ProofScriptEntry proofScriptEntry;

    @Nullable
    private Position position;

    @Nullable()
    public Term termOrSeq() {
        return termOrSeq;
    }

    public Problem setTermOrSeq(@Nullable() Term value) {
        termOrSeq = value;
        return this;
    }

    @Nullable()
    public String chooseContract() {
        return chooseContract;
    }

    public Problem setChooseContract(@Nullable() String value) {
        chooseContract = value;
        return this;
    }

    @Nullable()
    public String proofObligation() {
        return proofObligation;
    }

    public Problem setProofObligation(@Nullable() String value) {
        proofObligation = value;
        return this;
    }

    @Nullable()
    public ProofScriptEntry proofScriptEntry() {
        return proofScriptEntry;
    }

    public Problem setProofScriptEntry(@Nullable() ProofScriptEntry value) {
        proofScriptEntry = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public Problem setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public Problem(@Nullable Term termOrSeq, @Nullable String chooseContract, @Nullable String proofObligation, @Nullable ProofScriptEntry proofScriptEntry, @Nullable Position position) {
        this.termOrSeq = termOrSeq;
        this.chooseContract = chooseContract;
        this.proofObligation = proofObligation;
        this.proofScriptEntry = proofScriptEntry;
        this.position = position;
    }

    public Problem() {
        this.termOrSeq = null;
        this.chooseContract = null;
        this.proofObligation = null;
        this.proofScriptEntry = null;
        this.position = null;
    }

    public Problem(Problem other) {
        this(other.termOrSeq, other.chooseContract, other.proofObligation, other.proofScriptEntry, other.position);
    }

    public final static class Builder {

        @Nullable()
        public Term termOrSeq;

        @Nullable()
        public String chooseContract;

        @Nullable()
        public String proofObligation;

        @Nullable()
        public ProofScriptEntry proofScriptEntry;

        @Nullable()
        public Position position;

        public Problem build() {
            return new Problem(termOrSeq, chooseContract, proofObligation, proofScriptEntry, position);
        }

        public Builder termOrSeq(Term termOrSeq) {
            this.termOrSeq = termOrSeq;
            return this;
        }

        public Builder chooseContract(String chooseContract) {
            this.chooseContract = chooseContract;
            return this;
        }

        public Builder proofObligation(String proofObligation) {
            this.proofObligation = proofObligation;
            return this;
        }

        public Builder proofScriptEntry(ProofScriptEntry proofScriptEntry) {
            this.proofScriptEntry = proofScriptEntry;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.termOrSeq = termOrSeq;
        b.chooseContract = chooseContract;
        b.proofObligation = proofObligation;
        b.proofScriptEntry = proofScriptEntry;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Problem that))
            return false;
        return Objects.equals(termOrSeq, that.termOrSeq) && Objects.equals(chooseContract, that.chooseContract) && Objects.equals(proofObligation, that.proofObligation) && Objects.equals(proofScriptEntry, that.proofScriptEntry) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "Problem[termOrSeq=%s, chooseContract=%s, proofObligation=%s, proofScriptEntry=%s, position=%s]".formatted(termOrSeq, chooseContract, proofObligation, proofScriptEntry, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(termOrSeq, chooseContract, proofObligation, proofScriptEntry, position);
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
