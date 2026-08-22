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
public final class ReattachLoopInvariant extends JavaSourceElement implements ProgramTransformer {

    private final String name = "#reattachLoopInvariant";

    private final LoopStatment body;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public String name() {
        return name;
    }

    public LoopStatment body() {
        return body;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public ReattachLoopInvariant(LoopStatment body, @EqEx @Nullable PositionInfo positionInfo) {
        this.body = Objects.requireNonNull(body);
        this.positionInfo = positionInfo;
    }

    public ReattachLoopInvariant(LoopStatment body) {
        this.body = Objects.requireNonNull(body);
        this.positionInfo = null;
    }

    public ReattachLoopInvariant(ReattachLoopInvariant other) {
        this(other.body, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof ReattachLoopInvariant other))
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

    public ReattachLoopInvariant withBody(LoopStatment body) {
        return new ReattachLoopInvariant(name(), body, positionInfo());
    }

    public ReattachLoopInvariant withPositionInfo(PositionInfo positionInfo) {
        return new ReattachLoopInvariant(name(), body(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public LoopStatment body;

        @Nullable()
        public PositionInfo positionInfo;

        public ReattachLoopInvariant build() {
            return new ReattachLoopInvariant(body, positionInfo);
        }

        public Builder body(LoopStatment body) {
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
        b.body = body;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof ReattachLoopInvariant that))
            return false;
        return Objects.equals(name, that.name) && Objects.equals(body, that.body);
    }

    @Override()
    public String toString() {
        return "ReattachLoopInvariant[name=%s, body=%s, positionInfo=%s]".formatted(name, body, positionInfo);
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
