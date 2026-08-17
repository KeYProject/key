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
public final class ExecutionContext extends JavaSourceElement implements JavaProgramElement {

    private final TypeReference classContext;

    private final ReferencePrefix runtimeInstance;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public TypeReference classContext() {
        return classContext;
    }

    public ReferencePrefix runtimeInstance() {
        return runtimeInstance;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public ExecutionContext(TypeReference classContext, ReferencePrefix runtimeInstance, @EqEx @Nullable PositionInfo positionInfo) {
        this.classContext = Objects.requireNonNull(classContext);
        this.runtimeInstance = Objects.requireNonNull(runtimeInstance);
        this.positionInfo = positionInfo;
    }

    public ExecutionContext(TypeReference classContext, ReferencePrefix runtimeInstance) {
        this.classContext = Objects.requireNonNull(classContext);
        this.runtimeInstance = Objects.requireNonNull(runtimeInstance);
        this.positionInfo = null;
    }

    public ExecutionContext(ExecutionContext other) {
        this(other.classContext, other.runtimeInstance, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof ExecutionContext other))
            return null;
        cond = MatchHelper.match(classContext, other.classContext, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(runtimeInstance, other.runtimeInstance, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public ExecutionContext withClassContext(TypeReference classContext) {
        return new ExecutionContext(classContext, runtimeInstance(), positionInfo());
    }

    public ExecutionContext withRuntimeInstance(ReferencePrefix runtimeInstance) {
        return new ExecutionContext(classContext(), runtimeInstance, positionInfo());
    }

    public ExecutionContext withPositionInfo(PositionInfo positionInfo) {
        return new ExecutionContext(classContext(), runtimeInstance(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public TypeReference classContext;

        @Nullable()
        public ReferencePrefix runtimeInstance;

        @Nullable()
        public PositionInfo positionInfo;

        public ExecutionContext build() {
            return new ExecutionContext(classContext, runtimeInstance, positionInfo);
        }

        public Builder classContext(TypeReference classContext) {
            this.classContext = classContext;
            return this;
        }

        public Builder runtimeInstance(ReferencePrefix runtimeInstance) {
            this.runtimeInstance = runtimeInstance;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.classContext = classContext;
        b.runtimeInstance = runtimeInstance;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof ExecutionContext that))
            return false;
        return Objects.equals(classContext, that.classContext) && Objects.equals(runtimeInstance, that.runtimeInstance);
    }

    @Override()
    public String toString() {
        return "ExecutionContext[classContext=%s, runtimeInstance=%s, positionInfo=%s]".formatted(classContext, runtimeInstance, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(classContext, runtimeInstance);
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
