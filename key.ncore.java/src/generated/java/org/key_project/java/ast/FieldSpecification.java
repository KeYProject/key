package org.key_project.java.ast;

import org.jspecify.annotations.Nullable;
import de.uka.ilkd.key.speclang.jml.pretranslation.*;
import de.uka.ilkd.key.java.ast.PositionInfo;
import org.key_project.util.collection.*;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import org.key_project.logic.op.sv.*;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.Type;
import java.util.*;
import org.jspecify.annotations.NullMarked;

@NullMarked()
public final class FieldSpecification extends JavaSourceElement implements VariableSpecification {

    private final int dimensions;

    private final Expression initializer;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    private final IProgramVariable programVariable;

    private final Type type;

    @java.lang.Override()
    public int dimensions() {
        return dimensions;
    }

    @java.lang.Override()
    public Expression initializer() {
        return initializer;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    @java.lang.Override()
    public IProgramVariable programVariable() {
        return programVariable;
    }

    @java.lang.Override()
    public Type type() {
        return type;
    }

    public FieldSpecification(int dimensions, Expression initializer, @EqEx @Nullable PositionInfo positionInfo, IProgramVariable programVariable, Type type) {
        this.dimensions = Objects.requireNonNull(dimensions);
        this.initializer = Objects.requireNonNull(initializer);
        this.positionInfo = positionInfo;
        this.programVariable = Objects.requireNonNull(programVariable);
        this.type = Objects.requireNonNull(type);
    }

    public FieldSpecification(int dimensions, Expression initializer, IProgramVariable programVariable, Type type) {
        this.dimensions = Objects.requireNonNull(dimensions);
        this.initializer = Objects.requireNonNull(initializer);
        this.positionInfo = null;
        this.programVariable = Objects.requireNonNull(programVariable);
        this.type = Objects.requireNonNull(type);
    }

    public FieldSpecification(FieldSpecification other) {
        this(other.dimensions, other.initializer, other.positionInfo, other.programVariable, other.type);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof FieldSpecification other))
            return null;
        cond = MatchHelper.match(dimensions, other.dimensions, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(initializer, other.initializer, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(programVariable, other.programVariable, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(type, other.type, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public FieldSpecification withDimensions(int dimensions) {
        return new FieldSpecification(dimensions, initializer(), positionInfo(), programVariable(), type());
    }

    public FieldSpecification withInitializer(Expression initializer) {
        return new FieldSpecification(dimensions(), initializer, positionInfo(), programVariable(), type());
    }

    public FieldSpecification withPositionInfo(PositionInfo positionInfo) {
        return new FieldSpecification(dimensions(), initializer(), positionInfo, programVariable(), type());
    }

    public FieldSpecification withProgramVariable(IProgramVariable programVariable) {
        return new FieldSpecification(dimensions(), initializer(), positionInfo(), programVariable, type());
    }

    public FieldSpecification withType(Type type) {
        return new FieldSpecification(dimensions(), initializer(), positionInfo(), programVariable(), type);
    }

    public final static class Builder {

        @Nullable()
        public int dimensions;

        @Nullable()
        public Expression initializer;

        @Nullable()
        public PositionInfo positionInfo;

        @Nullable()
        public IProgramVariable programVariable;

        @Nullable()
        public Type type;

        public FieldSpecification build() {
            return new FieldSpecification(dimensions, initializer, positionInfo, programVariable, type);
        }

        public Builder dimensions(int dimensions) {
            this.dimensions = dimensions;
            return this;
        }

        public Builder initializer(Expression initializer) {
            this.initializer = initializer;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }

        public Builder programVariable(IProgramVariable programVariable) {
            this.programVariable = programVariable;
            return this;
        }

        public Builder type(Type type) {
            this.type = type;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.dimensions = dimensions;
        b.initializer = initializer;
        b.positionInfo = positionInfo;
        b.programVariable = programVariable;
        b.type = type;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof FieldSpecification that))
            return false;
        return Objects.equals(dimensions, that.dimensions) && Objects.equals(initializer, that.initializer) && Objects.equals(programVariable, that.programVariable) && Objects.equals(type, that.type);
    }

    @Override()
    public String toString() {
        return "FieldSpecification[dimensions=%s, initializer=%s, positionInfo=%s, programVariable=%s, type=%s]".formatted(dimensions, initializer, positionInfo, programVariable, type);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(dimensions, initializer, programVariable, type);
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
