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
public final class ConstructorDeclaration extends JavaSourceElement implements MethodDeclaration {

    private final StatementBlock body;

    private final Throws exceptions;

    private final JMLModifiers jmlModifiers;

    private final ProgramElementName name;

    private final ImmutableList<ParameterDeclaration> parameters;

    private final boolean parentIsInterfaceDeclaration;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    private final TypeReference returnType;

    private final Comment[] voidComments;

    @java.lang.Override()
    public StatementBlock body() {
        return body;
    }

    @java.lang.Override()
    public Throws exceptions() {
        return exceptions;
    }

    @java.lang.Override()
    public JMLModifiers jmlModifiers() {
        return jmlModifiers;
    }

    @java.lang.Override()
    public ProgramElementName name() {
        return name;
    }

    @java.lang.Override()
    public ImmutableList<ParameterDeclaration> parameters() {
        return parameters;
    }

    @java.lang.Override()
    public boolean parentIsInterfaceDeclaration() {
        return parentIsInterfaceDeclaration;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    @java.lang.Override()
    public TypeReference returnType() {
        return returnType;
    }

    @java.lang.Override()
    public Comment[] voidComments() {
        return voidComments;
    }

    public ConstructorDeclaration(StatementBlock body, Throws exceptions, JMLModifiers jmlModifiers, ProgramElementName name, ImmutableList<ParameterDeclaration> parameters, boolean parentIsInterfaceDeclaration, @EqEx @Nullable PositionInfo positionInfo, TypeReference returnType, Comment[] voidComments) {
        this.body = Objects.requireNonNull(body);
        this.exceptions = Objects.requireNonNull(exceptions);
        this.jmlModifiers = Objects.requireNonNull(jmlModifiers);
        this.name = Objects.requireNonNull(name);
        this.parameters = Objects.requireNonNull(parameters);
        this.parentIsInterfaceDeclaration = Objects.requireNonNull(parentIsInterfaceDeclaration);
        this.positionInfo = positionInfo;
        this.returnType = Objects.requireNonNull(returnType);
        this.voidComments = Objects.requireNonNull(voidComments);
    }

    public ConstructorDeclaration(StatementBlock body, Throws exceptions, JMLModifiers jmlModifiers, ProgramElementName name, ImmutableList<ParameterDeclaration> parameters, boolean parentIsInterfaceDeclaration, TypeReference returnType, Comment[] voidComments) {
        this.body = Objects.requireNonNull(body);
        this.exceptions = Objects.requireNonNull(exceptions);
        this.jmlModifiers = Objects.requireNonNull(jmlModifiers);
        this.name = Objects.requireNonNull(name);
        this.parameters = Objects.requireNonNull(parameters);
        this.parentIsInterfaceDeclaration = Objects.requireNonNull(parentIsInterfaceDeclaration);
        this.positionInfo = null;
        this.returnType = Objects.requireNonNull(returnType);
        this.voidComments = Objects.requireNonNull(voidComments);
    }

    public ConstructorDeclaration(ConstructorDeclaration other) {
        this(other.body, other.exceptions, other.jmlModifiers, other.name, other.parameters, other.parentIsInterfaceDeclaration, other.positionInfo, other.returnType, other.voidComments);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof ConstructorDeclaration other))
            return null;
        cond = MatchHelper.match(body, other.body, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(exceptions, other.exceptions, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(jmlModifiers, other.jmlModifiers, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(name, other.name, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(parameters, other.parameters, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(parentIsInterfaceDeclaration, other.parentIsInterfaceDeclaration, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(returnType, other.returnType, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(voidComments, other.voidComments, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public ConstructorDeclaration withBody(StatementBlock body) {
        return new ConstructorDeclaration(body, exceptions(), jmlModifiers(), name(), parameters(), parentIsInterfaceDeclaration(), positionInfo(), returnType(), voidComments());
    }

    public ConstructorDeclaration withExceptions(Throws exceptions) {
        return new ConstructorDeclaration(body(), exceptions, jmlModifiers(), name(), parameters(), parentIsInterfaceDeclaration(), positionInfo(), returnType(), voidComments());
    }

    public ConstructorDeclaration withJmlModifiers(JMLModifiers jmlModifiers) {
        return new ConstructorDeclaration(body(), exceptions(), jmlModifiers, name(), parameters(), parentIsInterfaceDeclaration(), positionInfo(), returnType(), voidComments());
    }

    public ConstructorDeclaration withName(ProgramElementName name) {
        return new ConstructorDeclaration(body(), exceptions(), jmlModifiers(), name, parameters(), parentIsInterfaceDeclaration(), positionInfo(), returnType(), voidComments());
    }

    public ConstructorDeclaration withParameters(ImmutableList<ParameterDeclaration> parameters) {
        return new ConstructorDeclaration(body(), exceptions(), jmlModifiers(), name(), parameters, parentIsInterfaceDeclaration(), positionInfo(), returnType(), voidComments());
    }

    public ConstructorDeclaration withParentIsInterfaceDeclaration(boolean parentIsInterfaceDeclaration) {
        return new ConstructorDeclaration(body(), exceptions(), jmlModifiers(), name(), parameters(), parentIsInterfaceDeclaration, positionInfo(), returnType(), voidComments());
    }

    public ConstructorDeclaration withPositionInfo(PositionInfo positionInfo) {
        return new ConstructorDeclaration(body(), exceptions(), jmlModifiers(), name(), parameters(), parentIsInterfaceDeclaration(), positionInfo, returnType(), voidComments());
    }

    public ConstructorDeclaration withReturnType(TypeReference returnType) {
        return new ConstructorDeclaration(body(), exceptions(), jmlModifiers(), name(), parameters(), parentIsInterfaceDeclaration(), positionInfo(), returnType, voidComments());
    }

    public ConstructorDeclaration withVoidComments(Comment[] voidComments) {
        return new ConstructorDeclaration(body(), exceptions(), jmlModifiers(), name(), parameters(), parentIsInterfaceDeclaration(), positionInfo(), returnType(), voidComments);
    }

    public final static class Builder {

        @Nullable()
        public StatementBlock body;

        @Nullable()
        public Throws exceptions;

        @Nullable()
        public JMLModifiers jmlModifiers;

        @Nullable()
        public ProgramElementName name;

        @Nullable()
        public ImmutableList<ParameterDeclaration> parameters;

        @Nullable()
        public boolean parentIsInterfaceDeclaration;

        @Nullable()
        public PositionInfo positionInfo;

        @Nullable()
        public TypeReference returnType;

        @Nullable()
        public Comment[] voidComments;

        public ConstructorDeclaration build() {
            return new ConstructorDeclaration(body, exceptions, jmlModifiers, name, parameters, parentIsInterfaceDeclaration, positionInfo, returnType, voidComments);
        }

        public Builder body(StatementBlock body) {
            this.body = body;
            return this;
        }

        public Builder exceptions(Throws exceptions) {
            this.exceptions = exceptions;
            return this;
        }

        public Builder jmlModifiers(JMLModifiers jmlModifiers) {
            this.jmlModifiers = jmlModifiers;
            return this;
        }

        public Builder name(ProgramElementName name) {
            this.name = name;
            return this;
        }

        public Builder parameters(ImmutableList<ParameterDeclaration> parameters) {
            this.parameters = parameters;
            return this;
        }

        public Builder parentIsInterfaceDeclaration(boolean parentIsInterfaceDeclaration) {
            this.parentIsInterfaceDeclaration = parentIsInterfaceDeclaration;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }

        public Builder returnType(TypeReference returnType) {
            this.returnType = returnType;
            return this;
        }

        public Builder voidComments(Comment[] voidComments) {
            this.voidComments = voidComments;
            return this;
        }

        public Builder parameters(ParameterDeclaration parameters) {
            if (this.parameters == null)
                this.parameters = new ArrayList<>();
            this.parameters.add(parameters);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.body = body;
        b.exceptions = exceptions;
        b.jmlModifiers = jmlModifiers;
        b.name = name;
        b.parameters = parameters;
        b.parentIsInterfaceDeclaration = parentIsInterfaceDeclaration;
        b.positionInfo = positionInfo;
        b.returnType = returnType;
        b.voidComments = voidComments;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof ConstructorDeclaration that))
            return false;
        return Objects.equals(body, that.body) && Objects.equals(exceptions, that.exceptions) && Objects.equals(jmlModifiers, that.jmlModifiers) && Objects.equals(name, that.name) && Objects.equals(parameters, that.parameters) && Objects.equals(parentIsInterfaceDeclaration, that.parentIsInterfaceDeclaration) && Objects.equals(returnType, that.returnType) && Objects.equals(voidComments, that.voidComments);
    }

    @Override()
    public String toString() {
        return "ConstructorDeclaration[body=%s, exceptions=%s, jmlModifiers=%s, name=%s, parameters=%s, parentIsInterfaceDeclaration=%s, positionInfo=%s, returnType=%s, voidComments=%s]".formatted(body, exceptions, jmlModifiers, name, parameters, parentIsInterfaceDeclaration, positionInfo, returnType, voidComments);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(body, exceptions, jmlModifiers, name, parameters, parentIsInterfaceDeclaration, returnType, voidComments);
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
