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
public final class FieldSpecification extends JavaSourceElement implements VariableSpecification {

    private final Type type;

    private final int dimensions;

    private final ProgramVariable var;

    @Nullable
    private final Expression init;

    private final Expression initializer;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    private final IProgramVariable programVariable;

    public Type type() {
        return type;
    }

    public int dimensions() {
        return dimensions;
    }

    public ProgramVariable var() {
        return var;
    }

    @Nullable()
    public Expression init() {
        return init;
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

    public FieldSpecification(Type type, int dimensions, ProgramVariable var, @Nullable Expression init, Expression initializer, @EqEx @Nullable PositionInfo positionInfo, IProgramVariable programVariable) {
        this.type = Objects.requireNonNull(type);
        this.dimensions = Objects.requireNonNull(dimensions);
        this.var = Objects.requireNonNull(var);
        this.init = init;
        this.initializer = Objects.requireNonNull(initializer);
        this.positionInfo = positionInfo;
        this.programVariable = Objects.requireNonNull(programVariable);
    }

    public FieldSpecification(Type type, int dimensions, ProgramVariable var, Expression initializer, IProgramVariable programVariable) {
        this.type = Objects.requireNonNull(type);
        this.dimensions = Objects.requireNonNull(dimensions);
        this.var = Objects.requireNonNull(var);
        this.init = null;
        this.initializer = Objects.requireNonNull(initializer);
        this.positionInfo = null;
        this.programVariable = Objects.requireNonNull(programVariable);
    }

    public FieldSpecification(FieldSpecification other) {
        this(other.type, other.dimensions, other.var, other.init, other.initializer, other.positionInfo, other.programVariable);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof FieldSpecification other))
            return null;
        cond = MatchHelper.match(type, other.type, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(dimensions, other.dimensions, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(var, other.var, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(init, other.init, cond);
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
        return cond;
    }

    public FieldSpecification withType(Type type) {
        return new FieldSpecification(type, dimensions(), var(), init(), initializer(), positionInfo(), programVariable());
    }

    public FieldSpecification withDimensions(int dimensions) {
        return new FieldSpecification(type(), dimensions, var(), init(), initializer(), positionInfo(), programVariable());
    }

    public FieldSpecification withVar(ProgramVariable var) {
        return new FieldSpecification(type(), dimensions(), var, init(), initializer(), positionInfo(), programVariable());
    }

    public FieldSpecification withInit(Expression init) {
        return new FieldSpecification(type(), dimensions(), var(), init, initializer(), positionInfo(), programVariable());
    }

    public FieldSpecification withInitializer(Expression initializer) {
        return new FieldSpecification(type(), dimensions(), var(), init(), initializer, positionInfo(), programVariable());
    }

    public FieldSpecification withPositionInfo(PositionInfo positionInfo) {
        return new FieldSpecification(type(), dimensions(), var(), init(), initializer(), positionInfo, programVariable());
    }

    public FieldSpecification withProgramVariable(IProgramVariable programVariable) {
        return new FieldSpecification(type(), dimensions(), var(), init(), initializer(), positionInfo(), programVariable);
    }

    public final static class Builder {

        @Nullable()
        public Type type;

        @Nullable()
        public int dimensions;

        @Nullable()
        public ProgramVariable var;

        @Nullable()
        public Expression init;

        @Nullable()
        public Expression initializer;

        @Nullable()
        public PositionInfo positionInfo;

        @Nullable()
        public IProgramVariable programVariable;

        public FieldSpecification build() {
            return new FieldSpecification(type, dimensions, var, init, initializer, positionInfo, programVariable);
        }

        public Builder type(Type type) {
            this.type = type;
            return this;
        }

        public Builder dimensions(int dimensions) {
            this.dimensions = dimensions;
            return this;
        }

        public Builder var(ProgramVariable var) {
            this.var = var;
            return this;
        }

        public Builder init(Expression init) {
            this.init = init;
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
    }

    public Builder builder() {
        Builder b = new Builder();
        b.type = type;
        b.dimensions = dimensions;
        b.var = var;
        b.init = init;
        b.initializer = initializer;
        b.positionInfo = positionInfo;
        b.programVariable = programVariable;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof FieldSpecification that))
            return false;
        return Objects.equals(type, that.type) && Objects.equals(dimensions, that.dimensions) && Objects.equals(var, that.var) && Objects.equals(init, that.init) && Objects.equals(initializer, that.initializer) && Objects.equals(programVariable, that.programVariable);
    }

    @Override()
    public String toString() {
        return "FieldSpecification[type=%s, dimensions=%s, var=%s, init=%s, initializer=%s, positionInfo=%s, programVariable=%s]".formatted(type, dimensions, var, init, initializer, positionInfo, programVariable);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(type, dimensions, var, init, initializer, programVariable);
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
