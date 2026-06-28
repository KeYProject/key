package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class ProofScriptEntry extends BaseAstNode {

    @Nullable
    private String scriptPath;

    @Nullable
    private ProofScript inlineScript;

    @Nullable
    private Position position;

    @Nullable()
    public String scriptPath() {
        return scriptPath;
    }

    public ProofScriptEntry setScriptPath(@Nullable() String value) {
        scriptPath = value;
        return this;
    }

    @Nullable()
    public ProofScript inlineScript() {
        return inlineScript;
    }

    public ProofScriptEntry setInlineScript(@Nullable() ProofScript value) {
        inlineScript = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public ProofScriptEntry setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public ProofScriptEntry(@Nullable String scriptPath, @Nullable ProofScript inlineScript, @Nullable Position position) {
        this.scriptPath = scriptPath;
        this.inlineScript = inlineScript;
        this.position = position;
    }

    public ProofScriptEntry() {
        this.scriptPath = null;
        this.inlineScript = null;
        this.position = null;
    }

    public ProofScriptEntry(ProofScriptEntry other) {
        this(other.scriptPath, other.inlineScript, other.position);
    }

    public final static class Builder {

        @Nullable()
        public String scriptPath;

        @Nullable()
        public ProofScript inlineScript;

        @Nullable()
        public Position position;

        public ProofScriptEntry build() {
            return new ProofScriptEntry(scriptPath, inlineScript, position);
        }

        public Builder scriptPath(String scriptPath) {
            this.scriptPath = scriptPath;
            return this;
        }

        public Builder inlineScript(ProofScript inlineScript) {
            this.inlineScript = inlineScript;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.scriptPath = scriptPath;
        b.inlineScript = inlineScript;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof ProofScriptEntry that))
            return false;
        return Objects.equals(scriptPath, that.scriptPath) && Objects.equals(inlineScript, that.inlineScript) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "ProofScriptEntry[scriptPath=%s, inlineScript=%s, position=%s]".formatted(scriptPath, inlineScript, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(scriptPath, inlineScript, position);
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
