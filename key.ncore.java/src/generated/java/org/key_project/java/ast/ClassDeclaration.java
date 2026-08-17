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
public final class ClassDeclaration extends JavaSourceElement implements TypeDeclaration {

    private final Extends extending;

    private final Implements implementing;

    private final boolean isInnerClass;

    private final boolean isLocalClass;

    private final boolean isAnonymousClass;

    private final ProgramElementName fullName;

    private final boolean isLibrary;

    private final JMLModifiers jmlModifiers;

    private final ImmutableList<MemberDeclaration> members;

    private final ProgramElementName name;

    private final boolean parentIsInterfaceDeclaration;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public Extends extending() {
        return extending;
    }

    public Implements implementing() {
        return implementing;
    }

    public boolean isInnerClass() {
        return isInnerClass;
    }

    public boolean isLocalClass() {
        return isLocalClass;
    }

    public boolean isAnonymousClass() {
        return isAnonymousClass;
    }

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

    public ClassDeclaration(Extends extending, Implements implementing, boolean isInnerClass, boolean isLocalClass, boolean isAnonymousClass, ProgramElementName fullName, boolean isLibrary, JMLModifiers jmlModifiers, ImmutableList<MemberDeclaration> members, ProgramElementName name, boolean parentIsInterfaceDeclaration, @EqEx @Nullable PositionInfo positionInfo) {
        this.extending = Objects.requireNonNull(extending);
        this.implementing = Objects.requireNonNull(implementing);
        this.isInnerClass = Objects.requireNonNull(isInnerClass);
        this.isLocalClass = Objects.requireNonNull(isLocalClass);
        this.isAnonymousClass = Objects.requireNonNull(isAnonymousClass);
        this.fullName = Objects.requireNonNull(fullName);
        this.isLibrary = Objects.requireNonNull(isLibrary);
        this.jmlModifiers = Objects.requireNonNull(jmlModifiers);
        this.members = Objects.requireNonNull(members);
        this.name = Objects.requireNonNull(name);
        this.parentIsInterfaceDeclaration = Objects.requireNonNull(parentIsInterfaceDeclaration);
        this.positionInfo = positionInfo;
    }

    public ClassDeclaration(Extends extending, Implements implementing, boolean isInnerClass, boolean isLocalClass, boolean isAnonymousClass, ProgramElementName fullName, boolean isLibrary, JMLModifiers jmlModifiers, ImmutableList<MemberDeclaration> members, ProgramElementName name, boolean parentIsInterfaceDeclaration) {
        this.extending = Objects.requireNonNull(extending);
        this.implementing = Objects.requireNonNull(implementing);
        this.isInnerClass = Objects.requireNonNull(isInnerClass);
        this.isLocalClass = Objects.requireNonNull(isLocalClass);
        this.isAnonymousClass = Objects.requireNonNull(isAnonymousClass);
        this.fullName = Objects.requireNonNull(fullName);
        this.isLibrary = Objects.requireNonNull(isLibrary);
        this.jmlModifiers = Objects.requireNonNull(jmlModifiers);
        this.members = Objects.requireNonNull(members);
        this.name = Objects.requireNonNull(name);
        this.parentIsInterfaceDeclaration = Objects.requireNonNull(parentIsInterfaceDeclaration);
        this.positionInfo = null;
    }

    public ClassDeclaration(ClassDeclaration other) {
        this(other.extending, other.implementing, other.isInnerClass, other.isLocalClass, other.isAnonymousClass, other.fullName, other.isLibrary, other.jmlModifiers, other.members, other.name, other.parentIsInterfaceDeclaration, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof ClassDeclaration other))
            return null;
        cond = MatchHelper.match(extending, other.extending, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(implementing, other.implementing, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(isInnerClass, other.isInnerClass, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(isLocalClass, other.isLocalClass, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(isAnonymousClass, other.isAnonymousClass, cond);
        if (cond == null) {
            return null;
        }
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

    public ClassDeclaration withExtending(Extends extending) {
        return new ClassDeclaration(extending, implementing(), isInnerClass(), isLocalClass(), isAnonymousClass(), fullName(), isLibrary(), jmlModifiers(), members(), name(), parentIsInterfaceDeclaration(), positionInfo());
    }

    public ClassDeclaration withImplementing(Implements implementing) {
        return new ClassDeclaration(extending(), implementing, isInnerClass(), isLocalClass(), isAnonymousClass(), fullName(), isLibrary(), jmlModifiers(), members(), name(), parentIsInterfaceDeclaration(), positionInfo());
    }

    public ClassDeclaration withIsInnerClass(boolean isInnerClass) {
        return new ClassDeclaration(extending(), implementing(), isInnerClass, isLocalClass(), isAnonymousClass(), fullName(), isLibrary(), jmlModifiers(), members(), name(), parentIsInterfaceDeclaration(), positionInfo());
    }

    public ClassDeclaration withIsLocalClass(boolean isLocalClass) {
        return new ClassDeclaration(extending(), implementing(), isInnerClass(), isLocalClass, isAnonymousClass(), fullName(), isLibrary(), jmlModifiers(), members(), name(), parentIsInterfaceDeclaration(), positionInfo());
    }

    public ClassDeclaration withIsAnonymousClass(boolean isAnonymousClass) {
        return new ClassDeclaration(extending(), implementing(), isInnerClass(), isLocalClass(), isAnonymousClass, fullName(), isLibrary(), jmlModifiers(), members(), name(), parentIsInterfaceDeclaration(), positionInfo());
    }

    public ClassDeclaration withFullName(ProgramElementName fullName) {
        return new ClassDeclaration(extending(), implementing(), isInnerClass(), isLocalClass(), isAnonymousClass(), fullName, isLibrary(), jmlModifiers(), members(), name(), parentIsInterfaceDeclaration(), positionInfo());
    }

    public ClassDeclaration withIsLibrary(boolean isLibrary) {
        return new ClassDeclaration(extending(), implementing(), isInnerClass(), isLocalClass(), isAnonymousClass(), fullName(), isLibrary, jmlModifiers(), members(), name(), parentIsInterfaceDeclaration(), positionInfo());
    }

    public ClassDeclaration withJmlModifiers(JMLModifiers jmlModifiers) {
        return new ClassDeclaration(extending(), implementing(), isInnerClass(), isLocalClass(), isAnonymousClass(), fullName(), isLibrary(), jmlModifiers, members(), name(), parentIsInterfaceDeclaration(), positionInfo());
    }

    public ClassDeclaration withMembers(ImmutableList<MemberDeclaration> members) {
        return new ClassDeclaration(extending(), implementing(), isInnerClass(), isLocalClass(), isAnonymousClass(), fullName(), isLibrary(), jmlModifiers(), members, name(), parentIsInterfaceDeclaration(), positionInfo());
    }

    public ClassDeclaration withName(ProgramElementName name) {
        return new ClassDeclaration(extending(), implementing(), isInnerClass(), isLocalClass(), isAnonymousClass(), fullName(), isLibrary(), jmlModifiers(), members(), name, parentIsInterfaceDeclaration(), positionInfo());
    }

    public ClassDeclaration withParentIsInterfaceDeclaration(boolean parentIsInterfaceDeclaration) {
        return new ClassDeclaration(extending(), implementing(), isInnerClass(), isLocalClass(), isAnonymousClass(), fullName(), isLibrary(), jmlModifiers(), members(), name(), parentIsInterfaceDeclaration, positionInfo());
    }

    public ClassDeclaration withPositionInfo(PositionInfo positionInfo) {
        return new ClassDeclaration(extending(), implementing(), isInnerClass(), isLocalClass(), isAnonymousClass(), fullName(), isLibrary(), jmlModifiers(), members(), name(), parentIsInterfaceDeclaration(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public Extends extending;

        @Nullable()
        public Implements implementing;

        @Nullable()
        public boolean isInnerClass;

        @Nullable()
        public boolean isLocalClass;

        @Nullable()
        public boolean isAnonymousClass;

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

        public ClassDeclaration build() {
            return new ClassDeclaration(extending, implementing, isInnerClass, isLocalClass, isAnonymousClass, fullName, isLibrary, jmlModifiers, members, name, parentIsInterfaceDeclaration, positionInfo);
        }

        public Builder extending(Extends extending) {
            this.extending = extending;
            return this;
        }

        public Builder implementing(Implements implementing) {
            this.implementing = implementing;
            return this;
        }

        public Builder isInnerClass(boolean isInnerClass) {
            this.isInnerClass = isInnerClass;
            return this;
        }

        public Builder isLocalClass(boolean isLocalClass) {
            this.isLocalClass = isLocalClass;
            return this;
        }

        public Builder isAnonymousClass(boolean isAnonymousClass) {
            this.isAnonymousClass = isAnonymousClass;
            return this;
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
            if (this.members == null) {
                this.members = ImmutableList.of(members);
                return this;
            }
            this.members = this.members.append(members);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.extending = extending;
        b.implementing = implementing;
        b.isInnerClass = isInnerClass;
        b.isLocalClass = isLocalClass;
        b.isAnonymousClass = isAnonymousClass;
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
        if (!(o instanceof ClassDeclaration that))
            return false;
        return Objects.equals(extending, that.extending) && Objects.equals(implementing, that.implementing) && Objects.equals(isInnerClass, that.isInnerClass) && Objects.equals(isLocalClass, that.isLocalClass) && Objects.equals(isAnonymousClass, that.isAnonymousClass) && Objects.equals(fullName, that.fullName) && Objects.equals(isLibrary, that.isLibrary) && Objects.equals(jmlModifiers, that.jmlModifiers) && Objects.equals(members, that.members) && Objects.equals(name, that.name) && Objects.equals(parentIsInterfaceDeclaration, that.parentIsInterfaceDeclaration);
    }

    @Override()
    public String toString() {
        return "ClassDeclaration[extending=%s, implementing=%s, isInnerClass=%s, isLocalClass=%s, isAnonymousClass=%s, fullName=%s, isLibrary=%s, jmlModifiers=%s, members=%s, name=%s, parentIsInterfaceDeclaration=%s, positionInfo=%s]".formatted(extending, implementing, isInnerClass, isLocalClass, isAnonymousClass, fullName, isLibrary, jmlModifiers, members, name, parentIsInterfaceDeclaration, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(extending, implementing, isInnerClass, isLocalClass, isAnonymousClass, fullName, isLibrary, jmlModifiers, members, name, parentIsInterfaceDeclaration);
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
