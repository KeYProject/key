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
public final class MethodDeclaration extends JavaSourceElement implements JavaDeclaration {

    private final TypeReference returnType;

    private final Comment[] voidComments;

    private final ProgramElementName name;

    private final ImmutableList<ParameterDeclaration> parameters;

    private final Throws exceptions;

    private final StatementBlock body;

    private final JMLModifiers jmlModifiers;

    private final boolean parentIsInterfaceDeclaration;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public TypeReference returnType() {
        return returnType;
    }

    public Comment[] voidComments() {
        return voidComments;
    }

    public ProgramElementName name() {
        return name;
    }

    public ImmutableList<ParameterDeclaration> parameters() {
        return parameters;
    }

    public Throws exceptions() {
        return exceptions;
    }

    public StatementBlock body() {
        return body;
    }

    public JMLModifiers jmlModifiers() {
        return jmlModifiers;
    }

    public boolean parentIsInterfaceDeclaration() {
        return parentIsInterfaceDeclaration;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public MethodDeclaration(TypeReference returnType, Comment[] voidComments, ProgramElementName name, ImmutableList<ParameterDeclaration> parameters, Throws exceptions, StatementBlock body, JMLModifiers jmlModifiers, boolean parentIsInterfaceDeclaration, @EqEx @Nullable PositionInfo positionInfo) {
        this.returnType = Objects.requireNonNull(returnType);
        this.voidComments = Objects.requireNonNull(voidComments);
        this.name = Objects.requireNonNull(name);
        this.parameters = Objects.requireNonNull(parameters);
        this.exceptions = Objects.requireNonNull(exceptions);
        this.body = Objects.requireNonNull(body);
        this.jmlModifiers = Objects.requireNonNull(jmlModifiers);
        this.parentIsInterfaceDeclaration = Objects.requireNonNull(parentIsInterfaceDeclaration);
        this.positionInfo = positionInfo;
    }

    public MethodDeclaration(TypeReference returnType, Comment[] voidComments, ProgramElementName name, ImmutableList<ParameterDeclaration> parameters, Throws exceptions, StatementBlock body, JMLModifiers jmlModifiers, boolean parentIsInterfaceDeclaration) {
        this.returnType = Objects.requireNonNull(returnType);
        this.voidComments = Objects.requireNonNull(voidComments);
        this.name = Objects.requireNonNull(name);
        this.parameters = Objects.requireNonNull(parameters);
        this.exceptions = Objects.requireNonNull(exceptions);
        this.body = Objects.requireNonNull(body);
        this.jmlModifiers = Objects.requireNonNull(jmlModifiers);
        this.parentIsInterfaceDeclaration = Objects.requireNonNull(parentIsInterfaceDeclaration);
        this.positionInfo = null;
    }

    public MethodDeclaration(MethodDeclaration other) {
        this(other.returnType, other.voidComments, other.name, other.parameters, other.exceptions, other.body, other.jmlModifiers, other.parentIsInterfaceDeclaration, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof MethodDeclaration other))
            return null;
        cond = MatchHelper.match(returnType, other.returnType, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(voidComments, other.voidComments, cond);
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
        cond = MatchHelper.match(exceptions, other.exceptions, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(body, other.body, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(jmlModifiers, other.jmlModifiers, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(parentIsInterfaceDeclaration, other.parentIsInterfaceDeclaration, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public MethodDeclaration withReturnType(TypeReference returnType) {
        return new MethodDeclaration(returnType, voidComments(), name(), parameters(), exceptions(), body(), jmlModifiers(), parentIsInterfaceDeclaration(), positionInfo());
    }

    public MethodDeclaration withVoidComments(Comment[] voidComments) {
        return new MethodDeclaration(returnType(), voidComments, name(), parameters(), exceptions(), body(), jmlModifiers(), parentIsInterfaceDeclaration(), positionInfo());
    }

    public MethodDeclaration withName(ProgramElementName name) {
        return new MethodDeclaration(returnType(), voidComments(), name, parameters(), exceptions(), body(), jmlModifiers(), parentIsInterfaceDeclaration(), positionInfo());
    }

    public MethodDeclaration withParameters(ImmutableList<ParameterDeclaration> parameters) {
        return new MethodDeclaration(returnType(), voidComments(), name(), parameters, exceptions(), body(), jmlModifiers(), parentIsInterfaceDeclaration(), positionInfo());
    }

    public MethodDeclaration withExceptions(Throws exceptions) {
        return new MethodDeclaration(returnType(), voidComments(), name(), parameters(), exceptions, body(), jmlModifiers(), parentIsInterfaceDeclaration(), positionInfo());
    }

    public MethodDeclaration withBody(StatementBlock body) {
        return new MethodDeclaration(returnType(), voidComments(), name(), parameters(), exceptions(), body, jmlModifiers(), parentIsInterfaceDeclaration(), positionInfo());
    }

    public MethodDeclaration withJmlModifiers(JMLModifiers jmlModifiers) {
        return new MethodDeclaration(returnType(), voidComments(), name(), parameters(), exceptions(), body(), jmlModifiers, parentIsInterfaceDeclaration(), positionInfo());
    }

    public MethodDeclaration withParentIsInterfaceDeclaration(boolean parentIsInterfaceDeclaration) {
        return new MethodDeclaration(returnType(), voidComments(), name(), parameters(), exceptions(), body(), jmlModifiers(), parentIsInterfaceDeclaration, positionInfo());
    }

    public MethodDeclaration withPositionInfo(PositionInfo positionInfo) {
        return new MethodDeclaration(returnType(), voidComments(), name(), parameters(), exceptions(), body(), jmlModifiers(), parentIsInterfaceDeclaration(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public TypeReference returnType;

        @Nullable()
        public Comment[] voidComments;

        @Nullable()
        public ProgramElementName name;

        @Nullable()
        public ImmutableList<ParameterDeclaration> parameters;

        @Nullable()
        public Throws exceptions;

        @Nullable()
        public StatementBlock body;

        @Nullable()
        public JMLModifiers jmlModifiers;

        @Nullable()
        public boolean parentIsInterfaceDeclaration;

        @Nullable()
        public PositionInfo positionInfo;

        public MethodDeclaration build() {
            return new MethodDeclaration(returnType, voidComments, name, parameters, exceptions, body, jmlModifiers, parentIsInterfaceDeclaration, positionInfo);
        }

        public Builder returnType(TypeReference returnType) {
            this.returnType = returnType;
            return this;
        }

        public Builder voidComments(Comment[] voidComments) {
            this.voidComments = voidComments;
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

        public Builder exceptions(Throws exceptions) {
            this.exceptions = exceptions;
            return this;
        }

        public Builder body(StatementBlock body) {
            this.body = body;
            return this;
        }

        public Builder jmlModifiers(JMLModifiers jmlModifiers) {
            this.jmlModifiers = jmlModifiers;
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

        public Builder parameters(ParameterDeclaration parameters) {
            if (this.parameters == null) {
                this.parameters = ImmutableList.of(parameters);
                return this;
            }
            this.parameters = this.parameters.append(parameters);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.returnType = returnType;
        b.voidComments = voidComments;
        b.name = name;
        b.parameters = parameters;
        b.exceptions = exceptions;
        b.body = body;
        b.jmlModifiers = jmlModifiers;
        b.parentIsInterfaceDeclaration = parentIsInterfaceDeclaration;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof MethodDeclaration that))
            return false;
        return Objects.equals(returnType, that.returnType) && Objects.equals(voidComments, that.voidComments) && Objects.equals(name, that.name) && Objects.equals(parameters, that.parameters) && Objects.equals(exceptions, that.exceptions) && Objects.equals(body, that.body) && Objects.equals(jmlModifiers, that.jmlModifiers) && Objects.equals(parentIsInterfaceDeclaration, that.parentIsInterfaceDeclaration);
    }

    @Override()
    public String toString() {
        return "MethodDeclaration[returnType=%s, voidComments=%s, name=%s, parameters=%s, exceptions=%s, body=%s, jmlModifiers=%s, parentIsInterfaceDeclaration=%s, positionInfo=%s]".formatted(returnType, voidComments, name, parameters, exceptions, body, jmlModifiers, parentIsInterfaceDeclaration, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(returnType, voidComments, name, parameters, exceptions, body, jmlModifiers, parentIsInterfaceDeclaration);
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
