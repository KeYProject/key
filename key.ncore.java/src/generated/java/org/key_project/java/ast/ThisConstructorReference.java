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
public final class ThisConstructorReference extends JavaSourceElement implements SpecialConstructorReference {

    private final ImmutableList<Expression> arguments;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    @java.lang.Override()
    public ImmutableList<Expression> arguments() {
        return arguments;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public ThisConstructorReference(ImmutableList<Expression> arguments, @EqEx @Nullable PositionInfo positionInfo) {
        this.arguments = Objects.requireNonNull(arguments);
        this.positionInfo = positionInfo;
    }

    public ThisConstructorReference(ImmutableList<Expression> arguments) {
        this.arguments = Objects.requireNonNull(arguments);
        this.positionInfo = null;
    }

    public ThisConstructorReference(ThisConstructorReference other) {
        this(other.arguments, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof ThisConstructorReference other))
            return null;
        cond = MatchHelper.match(arguments, other.arguments, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public ThisConstructorReference withArguments(ImmutableList<Expression> arguments) {
        return new ThisConstructorReference(arguments, positionInfo());
    }

    public ThisConstructorReference withPositionInfo(PositionInfo positionInfo) {
        return new ThisConstructorReference(arguments(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public ImmutableList<Expression> arguments;

        @Nullable()
        public PositionInfo positionInfo;

        public ThisConstructorReference build() {
            return new ThisConstructorReference(arguments, positionInfo);
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
        b.arguments = arguments;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof ThisConstructorReference that))
            return false;
        return Objects.equals(arguments, that.arguments);
    }

    @Override()
    public String toString() {
        return "ThisConstructorReference[arguments=%s, positionInfo=%s]".formatted(arguments, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(arguments);
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
