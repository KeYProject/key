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
public final class EnumClassDeclaration extends JavaSourceElement implements ClassDeclaration {

    private final Extends extending;

    @java.lang.Override()
    private final ProgramElementName fullName;

    private final Implements implementing;

    private final boolean isAnonymousClass;

    private final boolean isInnerClass;

    @java.lang.Override()
    private final boolean isLibrary;

    private final boolean isLocalClass;

    @java.lang.Override()
    private final JMLModifiers jmlModifiers;

    @java.lang.Override()
    private final ImmutableList<MemberDeclaration> members;

    @java.lang.Override()
    private final ProgramElementName name;

    @java.lang.Override()
    private final boolean parentIsInterfaceDeclaration;

    @EqEx
    @Nullable
    @java.lang.Override()
    private final PositionInfo positionInfo;

    @java.lang.Override()
    public Extends extending() {
        return extending;
    }

    @java.lang.Override()
    public ProgramElementName fullName() {
        return fullName;
    }

    @java.lang.Override()
    public Implements implementing() {
        return implementing;
    }

    @java.lang.Override()
    public boolean isAnonymousClass() {
        return isAnonymousClass;
    }

    @java.lang.Override()
    public boolean isInnerClass() {
        return isInnerClass;
    }

    @java.lang.Override()
    public boolean isLibrary() {
        return isLibrary;
    }

    @java.lang.Override()
    public boolean isLocalClass() {
        return isLocalClass;
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

    public EnumClassDeclaration(Extends extending, @java.lang.Override() ProgramElementName fullName, Implements implementing, boolean isAnonymousClass, boolean isInnerClass, @java.lang.Override() boolean isLibrary, boolean isLocalClass, @java.lang.Override() JMLModifiers jmlModifiers, @java.lang.Override() ImmutableList<MemberDeclaration> members, @java.lang.Override() ProgramElementName name, @java.lang.Override() boolean parentIsInterfaceDeclaration, @EqEx @Nullable @java.lang.Override() PositionInfo positionInfo) {
        this.extending = Objects.requireNonNull(extending);
        this.fullName = Objects.requireNonNull(fullName);
        this.implementing = Objects.requireNonNull(implementing);
        this.isAnonymousClass = Objects.requireNonNull(isAnonymousClass);
        this.isInnerClass = Objects.requireNonNull(isInnerClass);
        this.isLibrary = Objects.requireNonNull(isLibrary);
        this.isLocalClass = Objects.requireNonNull(isLocalClass);
        this.jmlModifiers = Objects.requireNonNull(jmlModifiers);
        this.members = Objects.requireNonNull(members);
        this.name = Objects.requireNonNull(name);
        this.parentIsInterfaceDeclaration = Objects.requireNonNull(parentIsInterfaceDeclaration);
        this.positionInfo = positionInfo;
    }

    public EnumClassDeclaration(Extends extending, @java.lang.Override() ProgramElementName fullName, Implements implementing, boolean isAnonymousClass, boolean isInnerClass, @java.lang.Override() boolean isLibrary, boolean isLocalClass, @java.lang.Override() JMLModifiers jmlModifiers, @java.lang.Override() ImmutableList<MemberDeclaration> members, @java.lang.Override() ProgramElementName name, @java.lang.Override() boolean parentIsInterfaceDeclaration) {
        this.extending = Objects.requireNonNull(extending);
        this.fullName = Objects.requireNonNull(fullName);
        this.implementing = Objects.requireNonNull(implementing);
        this.isAnonymousClass = Objects.requireNonNull(isAnonymousClass);
        this.isInnerClass = Objects.requireNonNull(isInnerClass);
        this.isLibrary = Objects.requireNonNull(isLibrary);
        this.isLocalClass = Objects.requireNonNull(isLocalClass);
        this.jmlModifiers = Objects.requireNonNull(jmlModifiers);
        this.members = Objects.requireNonNull(members);
        this.name = Objects.requireNonNull(name);
        this.parentIsInterfaceDeclaration = Objects.requireNonNull(parentIsInterfaceDeclaration);
        this.positionInfo = null;
    }

    public EnumClassDeclaration(EnumClassDeclaration other) {
        this(other.extending, other.fullName, other.implementing, other.isAnonymousClass, other.isInnerClass, other.isLibrary, other.isLocalClass, other.jmlModifiers, other.members, other.name, other.parentIsInterfaceDeclaration, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof EnumClassDeclaration other))
            return null;
        cond = MatchHelper.match(extending, other.extending, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(fullName, other.fullName, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(implementing, other.implementing, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(isAnonymousClass, other.isAnonymousClass, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(isInnerClass, other.isInnerClass, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(isLibrary, other.isLibrary, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(isLocalClass, other.isLocalClass, cond);
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

    public EnumClassDeclaration withExtending(Extends extending) {
        return new EnumClassDeclaration(extending, fullName(), implementing(), isAnonymousClass(), isInnerClass(), isLibrary(), isLocalClass(), jmlModifiers(), members(), name(), parentIsInterfaceDeclaration(), positionInfo());
    }

    public EnumClassDeclaration withFullName(ProgramElementName fullName) {
        return new EnumClassDeclaration(extending(), fullName, implementing(), isAnonymousClass(), isInnerClass(), isLibrary(), isLocalClass(), jmlModifiers(), members(), name(), parentIsInterfaceDeclaration(), positionInfo());
    }

    public EnumClassDeclaration withImplementing(Implements implementing) {
        return new EnumClassDeclaration(extending(), fullName(), implementing, isAnonymousClass(), isInnerClass(), isLibrary(), isLocalClass(), jmlModifiers(), members(), name(), parentIsInterfaceDeclaration(), positionInfo());
    }

    public EnumClassDeclaration withIsAnonymousClass(boolean isAnonymousClass) {
        return new EnumClassDeclaration(extending(), fullName(), implementing(), isAnonymousClass, isInnerClass(), isLibrary(), isLocalClass(), jmlModifiers(), members(), name(), parentIsInterfaceDeclaration(), positionInfo());
    }

    public EnumClassDeclaration withIsInnerClass(boolean isInnerClass) {
        return new EnumClassDeclaration(extending(), fullName(), implementing(), isAnonymousClass(), isInnerClass, isLibrary(), isLocalClass(), jmlModifiers(), members(), name(), parentIsInterfaceDeclaration(), positionInfo());
    }

    public EnumClassDeclaration withIsLibrary(boolean isLibrary) {
        return new EnumClassDeclaration(extending(), fullName(), implementing(), isAnonymousClass(), isInnerClass(), isLibrary, isLocalClass(), jmlModifiers(), members(), name(), parentIsInterfaceDeclaration(), positionInfo());
    }

    public EnumClassDeclaration withIsLocalClass(boolean isLocalClass) {
        return new EnumClassDeclaration(extending(), fullName(), implementing(), isAnonymousClass(), isInnerClass(), isLibrary(), isLocalClass, jmlModifiers(), members(), name(), parentIsInterfaceDeclaration(), positionInfo());
    }

    public EnumClassDeclaration withJmlModifiers(JMLModifiers jmlModifiers) {
        return new EnumClassDeclaration(extending(), fullName(), implementing(), isAnonymousClass(), isInnerClass(), isLibrary(), isLocalClass(), jmlModifiers, members(), name(), parentIsInterfaceDeclaration(), positionInfo());
    }

    public EnumClassDeclaration withMembers(ImmutableList<MemberDeclaration> members) {
        return new EnumClassDeclaration(extending(), fullName(), implementing(), isAnonymousClass(), isInnerClass(), isLibrary(), isLocalClass(), jmlModifiers(), members, name(), parentIsInterfaceDeclaration(), positionInfo());
    }

    public EnumClassDeclaration withName(ProgramElementName name) {
        return new EnumClassDeclaration(extending(), fullName(), implementing(), isAnonymousClass(), isInnerClass(), isLibrary(), isLocalClass(), jmlModifiers(), members(), name, parentIsInterfaceDeclaration(), positionInfo());
    }

    public EnumClassDeclaration withParentIsInterfaceDeclaration(boolean parentIsInterfaceDeclaration) {
        return new EnumClassDeclaration(extending(), fullName(), implementing(), isAnonymousClass(), isInnerClass(), isLibrary(), isLocalClass(), jmlModifiers(), members(), name(), parentIsInterfaceDeclaration, positionInfo());
    }

    public EnumClassDeclaration withPositionInfo(PositionInfo positionInfo) {
        return new EnumClassDeclaration(extending(), fullName(), implementing(), isAnonymousClass(), isInnerClass(), isLibrary(), isLocalClass(), jmlModifiers(), members(), name(), parentIsInterfaceDeclaration(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public Extends extending;

        @Nullable()
        public ProgramElementName fullName;

        @Nullable()
        public Implements implementing;

        @Nullable()
        public boolean isAnonymousClass;

        @Nullable()
        public boolean isInnerClass;

        @Nullable()
        public boolean isLibrary;

        @Nullable()
        public boolean isLocalClass;

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

        public EnumClassDeclaration build() {
            return new EnumClassDeclaration(extending, fullName, implementing, isAnonymousClass, isInnerClass, isLibrary, isLocalClass, jmlModifiers, members, name, parentIsInterfaceDeclaration, positionInfo);
        }

        public Builder extending(Extends extending) {
            this.extending = extending;
            return this;
        }

        public Builder fullName(ProgramElementName fullName) {
            this.fullName = fullName;
            return this;
        }

        public Builder implementing(Implements implementing) {
            this.implementing = implementing;
            return this;
        }

        public Builder isAnonymousClass(boolean isAnonymousClass) {
            this.isAnonymousClass = isAnonymousClass;
            return this;
        }

        public Builder isInnerClass(boolean isInnerClass) {
            this.isInnerClass = isInnerClass;
            return this;
        }

        public Builder isLibrary(boolean isLibrary) {
            this.isLibrary = isLibrary;
            return this;
        }

        public Builder isLocalClass(boolean isLocalClass) {
            this.isLocalClass = isLocalClass;
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
        b.extending = extending;
        b.fullName = fullName;
        b.implementing = implementing;
        b.isAnonymousClass = isAnonymousClass;
        b.isInnerClass = isInnerClass;
        b.isLibrary = isLibrary;
        b.isLocalClass = isLocalClass;
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
        if (!(o instanceof EnumClassDeclaration that))
            return false;
        return Objects.equals(extending, that.extending) && Objects.equals(fullName, that.fullName) && Objects.equals(implementing, that.implementing) && Objects.equals(isAnonymousClass, that.isAnonymousClass) && Objects.equals(isInnerClass, that.isInnerClass) && Objects.equals(isLibrary, that.isLibrary) && Objects.equals(isLocalClass, that.isLocalClass) && Objects.equals(jmlModifiers, that.jmlModifiers) && Objects.equals(members, that.members) && Objects.equals(name, that.name) && Objects.equals(parentIsInterfaceDeclaration, that.parentIsInterfaceDeclaration);
    }

    @Override()
    public String toString() {
        return "EnumClassDeclaration[extending=%s, fullName=%s, implementing=%s, isAnonymousClass=%s, isInnerClass=%s, isLibrary=%s, isLocalClass=%s, jmlModifiers=%s, members=%s, name=%s, parentIsInterfaceDeclaration=%s, positionInfo=%s]".formatted(extending, fullName, implementing, isAnonymousClass, isInnerClass, isLibrary, isLocalClass, jmlModifiers, members, name, parentIsInterfaceDeclaration, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(extending, fullName, implementing, isAnonymousClass, isInnerClass, isLibrary, isLocalClass, jmlModifiers, members, name, parentIsInterfaceDeclaration);
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
