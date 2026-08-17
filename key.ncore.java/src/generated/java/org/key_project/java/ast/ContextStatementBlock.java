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
public final class ContextStatementBlock extends JavaSourceElement implements StatementBlock {

    private final IExecutionContext executionContext;

    @Nullable
    private final MethodFrame innerMostMethodFrame;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    private final ImmutableList<Statement> statement;

    public IExecutionContext executionContext() {
        return executionContext;
    }

    @Nullable()
    @java.lang.Override()
    public MethodFrame innerMostMethodFrame() {
        return innerMostMethodFrame;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    @java.lang.Override()
    public ImmutableList<Statement> statement() {
        return statement;
    }

    public ContextStatementBlock(IExecutionContext executionContext, @Nullable MethodFrame innerMostMethodFrame, @EqEx @Nullable PositionInfo positionInfo, ImmutableList<Statement> statement) {
        this.executionContext = Objects.requireNonNull(executionContext);
        this.innerMostMethodFrame = innerMostMethodFrame;
        this.positionInfo = positionInfo;
        this.statement = Objects.requireNonNull(statement);
    }

    public ContextStatementBlock(IExecutionContext executionContext, ImmutableList<Statement> statement) {
        this.executionContext = Objects.requireNonNull(executionContext);
        this.innerMostMethodFrame = null;
        this.positionInfo = null;
        this.statement = Objects.requireNonNull(statement);
    }

    public ContextStatementBlock(ContextStatementBlock other) {
        this(other.executionContext, other.innerMostMethodFrame, other.positionInfo, other.statement);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof ContextStatementBlock other))
            return null;
        cond = MatchHelper.match(executionContext, other.executionContext, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(innerMostMethodFrame, other.innerMostMethodFrame, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(statement, other.statement, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public ContextStatementBlock withExecutionContext(IExecutionContext executionContext) {
        return new ContextStatementBlock(executionContext, innerMostMethodFrame(), positionInfo(), statement());
    }

    public ContextStatementBlock withInnerMostMethodFrame(MethodFrame innerMostMethodFrame) {
        return new ContextStatementBlock(executionContext(), innerMostMethodFrame, positionInfo(), statement());
    }

    public ContextStatementBlock withPositionInfo(PositionInfo positionInfo) {
        return new ContextStatementBlock(executionContext(), innerMostMethodFrame(), positionInfo, statement());
    }

    public ContextStatementBlock withStatement(ImmutableList<Statement> statement) {
        return new ContextStatementBlock(executionContext(), innerMostMethodFrame(), positionInfo(), statement);
    }

    public final static class Builder {

        @Nullable()
        public IExecutionContext executionContext;

        @Nullable()
        public MethodFrame innerMostMethodFrame;

        @Nullable()
        public PositionInfo positionInfo;

        @Nullable()
        public ImmutableList<Statement> statement;

        public ContextStatementBlock build() {
            return new ContextStatementBlock(executionContext, innerMostMethodFrame, positionInfo, statement);
        }

        public Builder executionContext(IExecutionContext executionContext) {
            this.executionContext = executionContext;
            return this;
        }

        public Builder innerMostMethodFrame(MethodFrame innerMostMethodFrame) {
            this.innerMostMethodFrame = innerMostMethodFrame;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }

        public Builder statement(ImmutableList<Statement> statement) {
            this.statement = statement;
            return this;
        }

        public Builder statement(Statement statement) {
            if (this.statement == null)
                this.statement = new ArrayList<>();
            this.statement.add(statement);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.executionContext = executionContext;
        b.innerMostMethodFrame = innerMostMethodFrame;
        b.positionInfo = positionInfo;
        b.statement = statement;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof ContextStatementBlock that))
            return false;
        return Objects.equals(executionContext, that.executionContext) && Objects.equals(innerMostMethodFrame, that.innerMostMethodFrame) && Objects.equals(statement, that.statement);
    }

    @Override()
    public String toString() {
        return "ContextStatementBlock[executionContext=%s, innerMostMethodFrame=%s, positionInfo=%s, statement=%s]".formatted(executionContext, innerMostMethodFrame, positionInfo, statement);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(executionContext, innerMostMethodFrame, statement);
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
