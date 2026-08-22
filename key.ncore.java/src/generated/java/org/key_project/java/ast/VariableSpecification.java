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
public final class VariableSpecification extends JavaSourceElement implements JavaProgramElement {

    private final Expression initializer;

    private final int dimensions;

    private final Type type;

    private final IProgramVariable programVariable;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public Expression initializer() {
        return initializer;
    }

    public int dimensions() {
        return dimensions;
    }

    public Type type() {
        return type;
    }

    public IProgramVariable programVariable() {
        return programVariable;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public VariableSpecification(Expression initializer, int dimensions, Type type, IProgramVariable programVariable, @EqEx @Nullable PositionInfo positionInfo) {
        this.initializer = Objects.requireNonNull(initializer);
        this.dimensions = Objects.requireNonNull(dimensions);
        this.type = Objects.requireNonNull(type);
        this.programVariable = Objects.requireNonNull(programVariable);
        this.positionInfo = positionInfo;
    }

    public VariableSpecification(Expression initializer, int dimensions, Type type, IProgramVariable programVariable) {
        this.initializer = Objects.requireNonNull(initializer);
        this.dimensions = Objects.requireNonNull(dimensions);
        this.type = Objects.requireNonNull(type);
        this.programVariable = Objects.requireNonNull(programVariable);
        this.positionInfo = null;
    }

    public VariableSpecification(VariableSpecification other) {
        this(other.initializer, other.dimensions, other.type, other.programVariable, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof VariableSpecification other))
            return null;
        cond = MatchHelper.match(initializer, other.initializer, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(dimensions, other.dimensions, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(type, other.type, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(programVariable, other.programVariable, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public VariableSpecification withInitializer(Expression initializer) {
        return new VariableSpecification(initializer, dimensions(), type(), programVariable(), positionInfo());
    }

    public VariableSpecification withDimensions(int dimensions) {
        return new VariableSpecification(initializer(), dimensions, type(), programVariable(), positionInfo());
    }

    public VariableSpecification withType(Type type) {
        return new VariableSpecification(initializer(), dimensions(), type, programVariable(), positionInfo());
    }

    public VariableSpecification withProgramVariable(IProgramVariable programVariable) {
        return new VariableSpecification(initializer(), dimensions(), type(), programVariable, positionInfo());
    }

    public VariableSpecification withPositionInfo(PositionInfo positionInfo) {
        return new VariableSpecification(initializer(), dimensions(), type(), programVariable(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public Expression initializer;

        @Nullable()
        public int dimensions;

        @Nullable()
        public Type type;

        @Nullable()
        public IProgramVariable programVariable;

        @Nullable()
        public PositionInfo positionInfo;

        public VariableSpecification build() {
            return new VariableSpecification(initializer, dimensions, type, programVariable, positionInfo);
        }

        public Builder initializer(Expression initializer) {
            this.initializer = initializer;
            return this;
        }

        public Builder dimensions(int dimensions) {
            this.dimensions = dimensions;
            return this;
        }

        public Builder type(Type type) {
            this.type = type;
            return this;
        }

        public Builder programVariable(IProgramVariable programVariable) {
            this.programVariable = programVariable;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.initializer = initializer;
        b.dimensions = dimensions;
        b.type = type;
        b.programVariable = programVariable;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof VariableSpecification that))
            return false;
        return Objects.equals(initializer, that.initializer) && Objects.equals(dimensions, that.dimensions) && Objects.equals(type, that.type) && Objects.equals(programVariable, that.programVariable);
    }

    @Override()
    public String toString() {
        return "VariableSpecification[initializer=%s, dimensions=%s, type=%s, programVariable=%s, positionInfo=%s]".formatted(initializer, dimensions, type, programVariable, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(initializer, dimensions, type, programVariable);
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
