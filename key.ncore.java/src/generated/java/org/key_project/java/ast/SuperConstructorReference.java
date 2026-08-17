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
public final class SuperConstructorReference extends JavaSourceElement implements SpecialConstructorReference {

    private final ReferencePrefix prefix;

    private final ImmutableList<Expression> arguments;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public ReferencePrefix prefix() {
        return prefix;
    }

    @java.lang.Override()
    public ImmutableList<Expression> arguments() {
        return arguments;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public SuperConstructorReference(ReferencePrefix prefix, ImmutableList<Expression> arguments, @EqEx @Nullable PositionInfo positionInfo) {
        this.prefix = Objects.requireNonNull(prefix);
        this.arguments = Objects.requireNonNull(arguments);
        this.positionInfo = positionInfo;
    }

    public SuperConstructorReference(ReferencePrefix prefix, ImmutableList<Expression> arguments) {
        this.prefix = Objects.requireNonNull(prefix);
        this.arguments = Objects.requireNonNull(arguments);
        this.positionInfo = null;
    }

    public SuperConstructorReference(SuperConstructorReference other) {
        this(other.prefix, other.arguments, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof SuperConstructorReference other))
            return null;
        cond = MatchHelper.match(prefix, other.prefix, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(arguments, other.arguments, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public SuperConstructorReference withPrefix(ReferencePrefix prefix) {
        return new SuperConstructorReference(prefix, arguments(), positionInfo());
    }

    public SuperConstructorReference withArguments(ImmutableList<Expression> arguments) {
        return new SuperConstructorReference(prefix(), arguments, positionInfo());
    }

    public SuperConstructorReference withPositionInfo(PositionInfo positionInfo) {
        return new SuperConstructorReference(prefix(), arguments(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public ReferencePrefix prefix;

        @Nullable()
        public ImmutableList<Expression> arguments;

        @Nullable()
        public PositionInfo positionInfo;

        public SuperConstructorReference build() {
            return new SuperConstructorReference(prefix, arguments, positionInfo);
        }

        public Builder prefix(ReferencePrefix prefix) {
            this.prefix = prefix;
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
            if (this.arguments == null) {
                this.arguments = ImmutableList.of(arguments);
                return this;
            }
            this.arguments = this.arguments.append(arguments);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.prefix = prefix;
        b.arguments = arguments;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof SuperConstructorReference that))
            return false;
        return Objects.equals(prefix, that.prefix) && Objects.equals(arguments, that.arguments);
    }

    @Override()
    public String toString() {
        return "SuperConstructorReference[prefix=%s, arguments=%s, positionInfo=%s]".formatted(prefix, arguments, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(prefix, arguments);
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
