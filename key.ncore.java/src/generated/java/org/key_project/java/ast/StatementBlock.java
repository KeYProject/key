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
public final class StatementBlock extends JavaSourceElement implements JavaStatement {

    private final ImmutableList<Statement> statement;

    @Nullable
    private final MethodFrame innerMostMethodFrame;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public ImmutableList<Statement> statement() {
        return statement;
    }

    @Nullable()
    public MethodFrame innerMostMethodFrame() {
        return innerMostMethodFrame;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public StatementBlock(ImmutableList<Statement> statement, @Nullable MethodFrame innerMostMethodFrame, @EqEx @Nullable PositionInfo positionInfo) {
        this.statement = Objects.requireNonNull(statement);
        this.innerMostMethodFrame = innerMostMethodFrame;
        this.positionInfo = positionInfo;
    }

    public StatementBlock(ImmutableList<Statement> statement) {
        this.statement = Objects.requireNonNull(statement);
        this.innerMostMethodFrame = null;
        this.positionInfo = null;
    }

    public StatementBlock(StatementBlock other) {
        this(other.statement, other.innerMostMethodFrame, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof StatementBlock other))
            return null;
        cond = MatchHelper.match(statement, other.statement, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(innerMostMethodFrame, other.innerMostMethodFrame, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public StatementBlock withStatement(ImmutableList<Statement> statement) {
        return new StatementBlock(statement, innerMostMethodFrame(), positionInfo());
    }

    public StatementBlock withInnerMostMethodFrame(MethodFrame innerMostMethodFrame) {
        return new StatementBlock(statement(), innerMostMethodFrame, positionInfo());
    }

    public StatementBlock withPositionInfo(PositionInfo positionInfo) {
        return new StatementBlock(statement(), innerMostMethodFrame(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public ImmutableList<Statement> statement;

        @Nullable()
        public MethodFrame innerMostMethodFrame;

        @Nullable()
        public PositionInfo positionInfo;

        public StatementBlock build() {
            return new StatementBlock(statement, innerMostMethodFrame, positionInfo);
        }

        public Builder statement(ImmutableList<Statement> statement) {
            this.statement = statement;
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

        public Builder statement(Statement statement) {
            if (this.statement == null) {
                this.statement = ImmutableList.of(statement);
                return this;
            }
            this.statement = this.statement.append(statement);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.statement = statement;
        b.innerMostMethodFrame = innerMostMethodFrame;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof StatementBlock that))
            return false;
        return Objects.equals(statement, that.statement) && Objects.equals(innerMostMethodFrame, that.innerMostMethodFrame);
    }

    @Override()
    public String toString() {
        return "StatementBlock[statement=%s, innerMostMethodFrame=%s, positionInfo=%s]".formatted(statement, innerMostMethodFrame, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(statement, innerMostMethodFrame);
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
