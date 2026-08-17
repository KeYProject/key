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
public final class Default extends JavaSourceElement {

    private final ImmutableList<Statement> body;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public ImmutableList<Statement> body() {
        return body;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public Default(ImmutableList<Statement> body, @EqEx @Nullable PositionInfo positionInfo) {
        this.body = Objects.requireNonNull(body);
        this.positionInfo = positionInfo;
    }

    public Default(ImmutableList<Statement> body) {
        this.body = Objects.requireNonNull(body);
        this.positionInfo = null;
    }

    public Default(Default other) {
        this(other.body, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof Default other))
            return null;
        cond = MatchHelper.match(body, other.body, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public Default withBody(ImmutableList<Statement> body) {
        return new Default(body, positionInfo());
    }

    public Default withPositionInfo(PositionInfo positionInfo) {
        return new Default(body(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public ImmutableList<Statement> body;

        @Nullable()
        public PositionInfo positionInfo;

        public Default build() {
            return new Default(body, positionInfo);
        }

        public Builder body(ImmutableList<Statement> body) {
            this.body = body;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }

        public Builder body(Statement body) {
            if (this.body == null)
                this.body = new ArrayList<>();
            this.body.add(body);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.body = body;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof Default that))
            return false;
        return Objects.equals(body, that.body);
    }

    @Override()
    public String toString() {
        return "Default[body=%s, positionInfo=%s]".formatted(body, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(body);
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
