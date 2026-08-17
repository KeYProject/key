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
public final class ArrayDeclaration extends JavaSourceElement implements TypeDeclaration {

    private final ProgramElementName fullName;

    private final boolean isLibrary;

    private final JMLModifiers jmlModifiers;

    private final ImmutableList<MemberDeclaration> members;

    private final ProgramElementName name;

    private final boolean parentIsInterfaceDeclaration;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    @java.lang.Override()
    public ProgramElementName fullName() {
        return fullName;
    }

    @java.lang.Override()
    public boolean isLibrary() {
        return isLibrary;
    }

    @java.lang.Override()
    public JMLModifiers jmlModifiers() {
        return jmlModifiers;
    }

    @java.lang.Override()
    public ImmutableList<MemberDeclaration> members() {
        return members;
    }

    @java.lang.Override()
    public ProgramElementName name() {
        return name;
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

    public ArrayDeclaration(ProgramElementName fullName, boolean isLibrary, JMLModifiers jmlModifiers, ImmutableList<MemberDeclaration> members, ProgramElementName name, boolean parentIsInterfaceDeclaration, @EqEx @Nullable PositionInfo positionInfo) {
        this.fullName = Objects.requireNonNull(fullName);
        this.isLibrary = Objects.requireNonNull(isLibrary);
        this.jmlModifiers = Objects.requireNonNull(jmlModifiers);
        this.members = Objects.requireNonNull(members);
        this.name = Objects.requireNonNull(name);
        this.parentIsInterfaceDeclaration = Objects.requireNonNull(parentIsInterfaceDeclaration);
        this.positionInfo = positionInfo;
    }

    public ArrayDeclaration(ProgramElementName fullName, boolean isLibrary, JMLModifiers jmlModifiers, ImmutableList<MemberDeclaration> members, ProgramElementName name, boolean parentIsInterfaceDeclaration) {
        this.fullName = Objects.requireNonNull(fullName);
        this.isLibrary = Objects.requireNonNull(isLibrary);
        this.jmlModifiers = Objects.requireNonNull(jmlModifiers);
        this.members = Objects.requireNonNull(members);
        this.name = Objects.requireNonNull(name);
        this.parentIsInterfaceDeclaration = Objects.requireNonNull(parentIsInterfaceDeclaration);
        this.positionInfo = null;
    }

    public ArrayDeclaration(ArrayDeclaration other) {
        this(other.fullName, other.isLibrary, other.jmlModifiers, other.members, other.name, other.parentIsInterfaceDeclaration, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof ArrayDeclaration other))
            return null;
        cond = MatchHelper.match(fullName, other.fullName, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(isLibrary, other.isLibrary, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(jmlModifiers, other.jmlModifiers, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(members, other.members, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(name, other.name, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(parentIsInterfaceDeclaration, other.parentIsInterfaceDeclaration, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public ArrayDeclaration withFullName(ProgramElementName fullName) {
        return new ArrayDeclaration(fullName, isLibrary(), jmlModifiers(), members(), name(), parentIsInterfaceDeclaration(), positionInfo());
    }

    public ArrayDeclaration withIsLibrary(boolean isLibrary) {
        return new ArrayDeclaration(fullName(), isLibrary, jmlModifiers(), members(), name(), parentIsInterfaceDeclaration(), positionInfo());
    }

    public ArrayDeclaration withJmlModifiers(JMLModifiers jmlModifiers) {
        return new ArrayDeclaration(fullName(), isLibrary(), jmlModifiers, members(), name(), parentIsInterfaceDeclaration(), positionInfo());
    }

    public ArrayDeclaration withMembers(ImmutableList<MemberDeclaration> members) {
        return new ArrayDeclaration(fullName(), isLibrary(), jmlModifiers(), members, name(), parentIsInterfaceDeclaration(), positionInfo());
    }

    public ArrayDeclaration withName(ProgramElementName name) {
        return new ArrayDeclaration(fullName(), isLibrary(), jmlModifiers(), members(), name, parentIsInterfaceDeclaration(), positionInfo());
    }

    public ArrayDeclaration withParentIsInterfaceDeclaration(boolean parentIsInterfaceDeclaration) {
        return new ArrayDeclaration(fullName(), isLibrary(), jmlModifiers(), members(), name(), parentIsInterfaceDeclaration, positionInfo());
    }

    public ArrayDeclaration withPositionInfo(PositionInfo positionInfo) {
        return new ArrayDeclaration(fullName(), isLibrary(), jmlModifiers(), members(), name(), parentIsInterfaceDeclaration(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public ProgramElementName fullName;

        @Nullable()
        public boolean isLibrary;

        @Nullable()
        public JMLModifiers jmlModifiers;

        @Nullable()
        public ImmutableList<MemberDeclaration> members;

        @Nullable()
        public ProgramElementName name;

        @Nullable()
        public boolean parentIsInterfaceDeclaration;

        @Nullable()
        public PositionInfo positionInfo;

        public ArrayDeclaration build() {
            return new ArrayDeclaration(fullName, isLibrary, jmlModifiers, members, name, parentIsInterfaceDeclaration, positionInfo);
        }

        public Builder fullName(ProgramElementName fullName) {
            this.fullName = fullName;
            return this;
        }

        public Builder isLibrary(boolean isLibrary) {
            this.isLibrary = isLibrary;
            return this;
        }

        public Builder jmlModifiers(JMLModifiers jmlModifiers) {
            this.jmlModifiers = jmlModifiers;
            return this;
        }

        public Builder members(ImmutableList<MemberDeclaration> members) {
            this.members = members;
            return this;
        }

        public Builder name(ProgramElementName name) {
            this.name = name;
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

        public Builder members(MemberDeclaration members) {
            if (this.members == null)
                this.members = new ArrayList<>();
            this.members.add(members);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.fullName = fullName;
        b.isLibrary = isLibrary;
        b.jmlModifiers = jmlModifiers;
        b.members = members;
        b.name = name;
        b.parentIsInterfaceDeclaration = parentIsInterfaceDeclaration;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof ArrayDeclaration that))
            return false;
        return Objects.equals(fullName, that.fullName) && Objects.equals(isLibrary, that.isLibrary) && Objects.equals(jmlModifiers, that.jmlModifiers) && Objects.equals(members, that.members) && Objects.equals(name, that.name) && Objects.equals(parentIsInterfaceDeclaration, that.parentIsInterfaceDeclaration);
    }

    @Override()
    public String toString() {
        return "ArrayDeclaration[fullName=%s, isLibrary=%s, jmlModifiers=%s, members=%s, name=%s, parentIsInterfaceDeclaration=%s, positionInfo=%s]".formatted(fullName, isLibrary, jmlModifiers, members, name, parentIsInterfaceDeclaration, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(fullName, isLibrary, jmlModifiers, members, name, parentIsInterfaceDeclaration);
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
