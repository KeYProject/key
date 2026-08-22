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
public final class SingleCatch extends JavaSourceElement {

    private final ParameterDeclaration parameter;

    private final StatementBlock body;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public ParameterDeclaration parameter() {
        return parameter;
    }

    public StatementBlock body() {
        return body;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public SingleCatch(ParameterDeclaration parameter, StatementBlock body, @EqEx @Nullable PositionInfo positionInfo) {
        this.parameter = Objects.requireNonNull(parameter);
        this.body = Objects.requireNonNull(body);
        this.positionInfo = positionInfo;
    }

    public SingleCatch(ParameterDeclaration parameter, StatementBlock body) {
        this.parameter = Objects.requireNonNull(parameter);
        this.body = Objects.requireNonNull(body);
        this.positionInfo = null;
    }

    public SingleCatch(SingleCatch other) {
        this(other.parameter, other.body, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof SingleCatch other))
            return null;
        cond = MatchHelper.match(parameter, other.parameter, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(body, other.body, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public SingleCatch withParameter(ParameterDeclaration parameter) {
        return new SingleCatch(parameter, body(), positionInfo());
    }

    public SingleCatch withBody(StatementBlock body) {
        return new SingleCatch(parameter(), body, positionInfo());
    }

    public SingleCatch withPositionInfo(PositionInfo positionInfo) {
        return new SingleCatch(parameter(), body(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public ParameterDeclaration parameter;

        @Nullable()
        public StatementBlock body;

        @Nullable()
        public PositionInfo positionInfo;

        public SingleCatch build() {
            return new SingleCatch(parameter, body, positionInfo);
        }

        public Builder parameter(ParameterDeclaration parameter) {
            this.parameter = parameter;
            return this;
        }

        public Builder body(StatementBlock body) {
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
        b.parameter = parameter;
        b.body = body;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof SingleCatch that))
            return false;
        return Objects.equals(parameter, that.parameter) && Objects.equals(body, that.body);
    }

    @Override()
    public String toString() {
        return "SingleCatch[parameter=%s, body=%s, positionInfo=%s]".formatted(parameter, body, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(parameter, body);
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
