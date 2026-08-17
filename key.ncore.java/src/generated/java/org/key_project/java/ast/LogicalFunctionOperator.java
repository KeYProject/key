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
public final class LogicalFunctionOperator extends JavaSourceElement implements Operator {

    private final LogicFunction function;

    private final ImmutableList<Expression> arguments;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public LogicFunction function() {
        return function;
    }

    public ImmutableList<Expression> arguments() {
        return arguments;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public LogicalFunctionOperator(LogicFunction function, ImmutableList<Expression> arguments, @EqEx @Nullable PositionInfo positionInfo) {
        this.function = Objects.requireNonNull(function);
        this.arguments = Objects.requireNonNull(arguments);
        this.positionInfo = positionInfo;
    }

    public LogicalFunctionOperator(LogicFunction function, ImmutableList<Expression> arguments) {
        this.function = Objects.requireNonNull(function);
        this.arguments = Objects.requireNonNull(arguments);
        this.positionInfo = null;
    }

    public LogicalFunctionOperator(LogicalFunctionOperator other) {
        this(other.function, other.arguments, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof LogicalFunctionOperator other))
            return null;
        cond = MatchHelper.match(function, other.function, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(arguments, other.arguments, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public LogicalFunctionOperator withFunction(LogicFunction function) {
        return new LogicalFunctionOperator(function, arguments(), positionInfo());
    }

    public LogicalFunctionOperator withArguments(ImmutableList<Expression> arguments) {
        return new LogicalFunctionOperator(function(), arguments, positionInfo());
    }

    public LogicalFunctionOperator withPositionInfo(PositionInfo positionInfo) {
        return new LogicalFunctionOperator(function(), arguments(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public LogicFunction function;

        @Nullable()
        public ImmutableList<Expression> arguments;

        @Nullable()
        public PositionInfo positionInfo;

        public LogicalFunctionOperator build() {
            return new LogicalFunctionOperator(function, arguments, positionInfo);
        }

        public Builder function(LogicFunction function) {
            this.function = function;
            return this;
        }

        public Builder arguments(ImmutableList<Expression> arguments) {
            this.arguments = arguments;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }

        public Builder arguments(Expression arguments) {
            if (this.arguments == null)
                this.arguments = new ArrayList<>();
            this.arguments.add(arguments);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.function = function;
        b.arguments = arguments;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof LogicalFunctionOperator that))
            return false;
        return Objects.equals(function, that.function) && Objects.equals(arguments, that.arguments);
    }

    @Override()
    public String toString() {
        return "LogicalFunctionOperator[function=%s, arguments=%s, positionInfo=%s]".formatted(function, arguments, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(function, arguments);
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
