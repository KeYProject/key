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
public final class MethodCall extends JavaSourceElement implements ProgramTransformer {

    private final MethodReference methRef;

    private final ReferencePrefix newContext;

    private final ProgramVariable pvar;

    private final ImmutableList<Expression> arguments;

    private final KeYJavaType staticPrefixType;

    private final ProgramElement body;

    private final String name;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public MethodReference methRef() {
        return methRef;
    }

    public ReferencePrefix newContext() {
        return newContext;
    }

    public ProgramVariable pvar() {
        return pvar;
    }

    public ImmutableList<Expression> arguments() {
        return arguments;
    }

    public KeYJavaType staticPrefixType() {
        return staticPrefixType;
    }

    @java.lang.Override()
    public ProgramElement body() {
        return body;
    }

    @java.lang.Override()
    public String name() {
        return name;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public MethodCall(MethodReference methRef, ReferencePrefix newContext, ProgramVariable pvar, ImmutableList<Expression> arguments, KeYJavaType staticPrefixType, ProgramElement body, String name, @EqEx @Nullable PositionInfo positionInfo) {
        this.methRef = Objects.requireNonNull(methRef);
        this.newContext = Objects.requireNonNull(newContext);
        this.pvar = Objects.requireNonNull(pvar);
        this.arguments = Objects.requireNonNull(arguments);
        this.staticPrefixType = Objects.requireNonNull(staticPrefixType);
        this.body = Objects.requireNonNull(body);
        this.name = Objects.requireNonNull(name);
        this.positionInfo = positionInfo;
    }

    public MethodCall(MethodReference methRef, ReferencePrefix newContext, ProgramVariable pvar, ImmutableList<Expression> arguments, KeYJavaType staticPrefixType, ProgramElement body, String name) {
        this.methRef = Objects.requireNonNull(methRef);
        this.newContext = Objects.requireNonNull(newContext);
        this.pvar = Objects.requireNonNull(pvar);
        this.arguments = Objects.requireNonNull(arguments);
        this.staticPrefixType = Objects.requireNonNull(staticPrefixType);
        this.body = Objects.requireNonNull(body);
        this.name = Objects.requireNonNull(name);
        this.positionInfo = null;
    }

    public MethodCall(MethodCall other) {
        this(other.methRef, other.newContext, other.pvar, other.arguments, other.staticPrefixType, other.body, other.name, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof MethodCall other))
            return null;
        cond = MatchHelper.match(methRef, other.methRef, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(newContext, other.newContext, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(pvar, other.pvar, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(arguments, other.arguments, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(staticPrefixType, other.staticPrefixType, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(body, other.body, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(name, other.name, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public MethodCall withMethRef(MethodReference methRef) {
        return new MethodCall(methRef, newContext(), pvar(), arguments(), staticPrefixType(), body(), name(), positionInfo());
    }

    public MethodCall withNewContext(ReferencePrefix newContext) {
        return new MethodCall(methRef(), newContext, pvar(), arguments(), staticPrefixType(), body(), name(), positionInfo());
    }

    public MethodCall withPvar(ProgramVariable pvar) {
        return new MethodCall(methRef(), newContext(), pvar, arguments(), staticPrefixType(), body(), name(), positionInfo());
    }

    public MethodCall withArguments(ImmutableList<Expression> arguments) {
        return new MethodCall(methRef(), newContext(), pvar(), arguments, staticPrefixType(), body(), name(), positionInfo());
    }

    public MethodCall withStaticPrefixType(KeYJavaType staticPrefixType) {
        return new MethodCall(methRef(), newContext(), pvar(), arguments(), staticPrefixType, body(), name(), positionInfo());
    }

    public MethodCall withBody(ProgramElement body) {
        return new MethodCall(methRef(), newContext(), pvar(), arguments(), staticPrefixType(), body, name(), positionInfo());
    }

    public MethodCall withName(String name) {
        return new MethodCall(methRef(), newContext(), pvar(), arguments(), staticPrefixType(), body(), name, positionInfo());
    }

    public MethodCall withPositionInfo(PositionInfo positionInfo) {
        return new MethodCall(methRef(), newContext(), pvar(), arguments(), staticPrefixType(), body(), name(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public MethodReference methRef;

        @Nullable()
        public ReferencePrefix newContext;

        @Nullable()
        public ProgramVariable pvar;

        @Nullable()
        public ImmutableList<Expression> arguments;

        @Nullable()
        public KeYJavaType staticPrefixType;

        @Nullable()
        public ProgramElement body;

        @Nullable()
        public String name;

        @Nullable()
        public PositionInfo positionInfo;

        public MethodCall build() {
            return new MethodCall(methRef, newContext, pvar, arguments, staticPrefixType, body, name, positionInfo);
        }

        public Builder methRef(MethodReference methRef) {
            this.methRef = methRef;
            return this;
        }

        public Builder newContext(ReferencePrefix newContext) {
            this.newContext = newContext;
            return this;
        }

        public Builder pvar(ProgramVariable pvar) {
            this.pvar = pvar;
            return this;
        }

        public Builder arguments(ImmutableList<Expression> arguments) {
            this.arguments = arguments;
            return this;
        }

        public Builder staticPrefixType(KeYJavaType staticPrefixType) {
            this.staticPrefixType = staticPrefixType;
            return this;
        }

        public Builder body(ProgramElement body) {
            this.body = body;
            return this;
        }

        public Builder name(String name) {
            this.name = name;
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
        b.methRef = methRef;
        b.newContext = newContext;
        b.pvar = pvar;
        b.arguments = arguments;
        b.staticPrefixType = staticPrefixType;
        b.body = body;
        b.name = name;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof MethodCall that))
            return false;
        return Objects.equals(methRef, that.methRef) && Objects.equals(newContext, that.newContext) && Objects.equals(pvar, that.pvar) && Objects.equals(arguments, that.arguments) && Objects.equals(staticPrefixType, that.staticPrefixType) && Objects.equals(body, that.body) && Objects.equals(name, that.name);
    }

    @Override()
    public String toString() {
        return "MethodCall[methRef=%s, newContext=%s, pvar=%s, arguments=%s, staticPrefixType=%s, body=%s, name=%s, positionInfo=%s]".formatted(methRef, newContext, pvar, arguments, staticPrefixType, body, name, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(methRef, newContext, pvar, arguments, staticPrefixType, body, name);
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
