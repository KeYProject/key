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
public final class MethodReference extends JavaSourceElement implements JavaProgramElement {

    private final ReferencePrefix prefix;

    private final MethodName name;

    private final ImmutableList<? extends Expression> arguments;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public ReferencePrefix prefix() {
        return prefix;
    }

    public MethodName name() {
        return name;
    }

    public ImmutableList<? extends Expression> arguments() {
        return arguments;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public MethodReference(ReferencePrefix prefix, MethodName name, ImmutableList<? extends Expression> arguments, @EqEx @Nullable PositionInfo positionInfo) {
        this.prefix = Objects.requireNonNull(prefix);
        this.name = Objects.requireNonNull(name);
        this.arguments = Objects.requireNonNull(arguments);
        this.positionInfo = positionInfo;
    }

    public MethodReference(ReferencePrefix prefix, MethodName name, ImmutableList<? extends Expression> arguments) {
        this.prefix = Objects.requireNonNull(prefix);
        this.name = Objects.requireNonNull(name);
        this.arguments = Objects.requireNonNull(arguments);
        this.positionInfo = null;
    }

    public MethodReference(MethodReference other) {
        this(other.prefix, other.name, other.arguments, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof MethodReference other))
            return null;
        cond = MatchHelper.match(prefix, other.prefix, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(name, other.name, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(arguments, other.arguments, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public MethodReference withPrefix(ReferencePrefix prefix) {
        return new MethodReference(prefix, name(), arguments(), positionInfo());
    }

    public MethodReference withName(MethodName name) {
        return new MethodReference(prefix(), name, arguments(), positionInfo());
    }

    public MethodReference withArguments(ImmutableList<? extends Expression> arguments) {
        return new MethodReference(prefix(), name(), arguments, positionInfo());
    }

    public MethodReference withPositionInfo(PositionInfo positionInfo) {
        return new MethodReference(prefix(), name(), arguments(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public ReferencePrefix prefix;

        @Nullable()
        public MethodName name;

        @Nullable()
        public ImmutableList<? extends Expression> arguments;

        @Nullable()
        public PositionInfo positionInfo;

        public MethodReference build() {
            return new MethodReference(prefix, name, arguments, positionInfo);
        }

        public Builder prefix(ReferencePrefix prefix) {
            this.prefix = prefix;
            return this;
        }

        public Builder name(MethodName name) {
            this.name = name;
            return this;
        }

        public Builder arguments(ImmutableList<? extends Expression> arguments) {
            this.arguments = arguments;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }

        public Builder arguments(? extends Expression arguments) {
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
        b.name = name;
        b.arguments = arguments;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof MethodReference that))
            return false;
        return Objects.equals(prefix, that.prefix) && Objects.equals(name, that.name) && Objects.equals(arguments, that.arguments);
    }

    @Override()
    public String toString() {
        return "MethodReference[prefix=%s, name=%s, arguments=%s, positionInfo=%s]".formatted(prefix, name, arguments, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(prefix, name, arguments);
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
