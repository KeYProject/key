package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class ProofScript extends BaseAstNode {

    private List<ProofScriptCommand> commands;

    @Nullable
    private Position position;

    public List<ProofScriptCommand> commands() {
        return commands;
    }

    public ProofScript setCommands(List<ProofScriptCommand> value) {
        commands = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public ProofScript setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public ProofScript(List<ProofScriptCommand> commands, @Nullable Position position) {
        this.commands = Objects.requireNonNull(commands);
        this.position = position;
    }

    public ProofScript(List<ProofScriptCommand> commands) {
        this.commands = Objects.requireNonNull(commands);
        this.position = null;
    }

    public ProofScript(ProofScript other) {
        this(other.commands, other.position);
    }

    public final static class Builder {

        @Nullable()
        public List<ProofScriptCommand> commands;

        @Nullable()
        public Position position;

        public ProofScript build() {
            return new ProofScript(commands, position);
        }

        public Builder commands(List<ProofScriptCommand> commands) {
            this.commands = commands;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder commands(ProofScriptCommand commands) {
            if (this.commands == null)
                this.commands = new ArrayList<>();
            this.commands.add(commands);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.commands = commands;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof ProofScript that))
            return false;
        return Objects.equals(commands, that.commands) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "ProofScript[commands=%s, position=%s]".formatted(commands, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(commands, position);
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
