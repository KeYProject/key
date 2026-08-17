package org.key_project.java.ast;

import org.jspecify.annotations.Nullable;
import de.uka.ilkd.key.speclang.jml.pretranslation.*;
import de.uka.ilkd.key.java.ast.PositionInfo;
import org.key_project.util.collection.*;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import org.key_project.logic.op.sv.*;
import de.uka.ilkd.key.java.Services;
import java.util.*;
import org.jspecify.annotations.NullMarked;

@NullMarked()
public final class LabeledStatement extends JavaSourceElement implements JavaStatement {

    private final Label name;

    private final Statement body;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public Label name() {
        return name;
    }

    public Statement body() {
        return body;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public LabeledStatement(Label name, Statement body, @EqEx @Nullable PositionInfo positionInfo) {
        this.name = Objects.requireNonNull(name);
        this.body = Objects.requireNonNull(body);
        this.positionInfo = positionInfo;
    }

    public LabeledStatement(Label name, Statement body) {
        this.name = Objects.requireNonNull(name);
        this.body = Objects.requireNonNull(body);
        this.positionInfo = null;
    }

    public LabeledStatement(LabeledStatement other) {
        this(other.name, other.body, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof LabeledStatement other))
            return null;
        cond = MatchHelper.match(name, other.name, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(body, other.body, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public LabeledStatement withName(Label name) {
        return new LabeledStatement(name, body(), positionInfo());
    }

    public LabeledStatement withBody(Statement body) {
        return new LabeledStatement(name(), body, positionInfo());
    }

    public LabeledStatement withPositionInfo(PositionInfo positionInfo) {
        return new LabeledStatement(name(), body(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public Label name;

        @Nullable()
        public Statement body;

        @Nullable()
        public PositionInfo positionInfo;

        public LabeledStatement build() {
            return new LabeledStatement(name, body, positionInfo);
        }

        public Builder name(Label name) {
            this.name = name;
            return this;
        }

        public Builder body(Statement body) {
            this.body = body;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.name = name;
        b.body = body;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof LabeledStatement that))
            return false;
        return Objects.equals(name, that.name) && Objects.equals(body, that.body);
    }

    @Override()
    public String toString() {
        return "LabeledStatement[name=%s, body=%s, positionInfo=%s]".formatted(name, body, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(name, body);
        return hashCode;
    }

    public <R> R accept(org.key_project.java.ast.visitor.Visitor<R> visitor) {
        return visitor.visit(this);
    }

    public <R, A> R accept(org.key_project.java.ast.visitor.ArgVisitor<R, A> visitor, A arg) {
        return visitor.visit(this, arg);
    }

    public void accept(org.key_project.java.ast.visitor.VoidVisitor visitor) {
        visitor.visit(this);
    }
}
