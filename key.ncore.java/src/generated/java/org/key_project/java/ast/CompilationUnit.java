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
public final class CompilationUnit extends JavaSourceElement implements JavaProgramElement {

    @Nullable
    private final PackageReference packageReference;

    private final ImmutableList<Import> imports;

    private final ImmutableList<TypeDeclaration> typeDeclarations;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    @Nullable()
    public PackageReference packageReference() {
        return packageReference;
    }

    public ImmutableList<Import> imports() {
        return imports;
    }

    public ImmutableList<TypeDeclaration> typeDeclarations() {
        return typeDeclarations;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public CompilationUnit(@Nullable PackageReference packageReference, ImmutableList<Import> imports, ImmutableList<TypeDeclaration> typeDeclarations, @EqEx @Nullable PositionInfo positionInfo) {
        this.packageReference = packageReference;
        this.imports = Objects.requireNonNull(imports);
        this.typeDeclarations = Objects.requireNonNull(typeDeclarations);
        this.positionInfo = positionInfo;
    }

    public CompilationUnit(ImmutableList<Import> imports, ImmutableList<TypeDeclaration> typeDeclarations) {
        this.packageReference = null;
        this.imports = Objects.requireNonNull(imports);
        this.typeDeclarations = Objects.requireNonNull(typeDeclarations);
        this.positionInfo = null;
    }

    public CompilationUnit(CompilationUnit other) {
        this(other.packageReference, other.imports, other.typeDeclarations, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof CompilationUnit other))
            return null;
        cond = MatchHelper.match(packageReference, other.packageReference, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(imports, other.imports, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(typeDeclarations, other.typeDeclarations, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public CompilationUnit withPackageReference(PackageReference packageReference) {
        return new CompilationUnit(packageReference, imports(), typeDeclarations(), positionInfo());
    }

    public CompilationUnit withImports(ImmutableList<Import> imports) {
        return new CompilationUnit(packageReference(), imports, typeDeclarations(), positionInfo());
    }

    public CompilationUnit withTypeDeclarations(ImmutableList<TypeDeclaration> typeDeclarations) {
        return new CompilationUnit(packageReference(), imports(), typeDeclarations, positionInfo());
    }

    public CompilationUnit withPositionInfo(PositionInfo positionInfo) {
        return new CompilationUnit(packageReference(), imports(), typeDeclarations(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public PackageReference packageReference;

        @Nullable()
        public ImmutableList<Import> imports;

        @Nullable()
        public ImmutableList<TypeDeclaration> typeDeclarations;

        @Nullable()
        public PositionInfo positionInfo;

        public CompilationUnit build() {
            return new CompilationUnit(packageReference, imports, typeDeclarations, positionInfo);
        }

        public Builder packageReference(PackageReference packageReference) {
            this.packageReference = packageReference;
            return this;
        }

        public Builder imports(ImmutableList<Import> imports) {
            this.imports = imports;
            return this;
        }

        public Builder typeDeclarations(ImmutableList<TypeDeclaration> typeDeclarations) {
            this.typeDeclarations = typeDeclarations;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }

        public Builder imports(Import imports) {
            if (this.imports == null)
                this.imports = new ArrayList<>();
            this.imports.add(imports);
            return this;
        }

        public Builder typeDeclarations(TypeDeclaration typeDeclarations) {
            if (this.typeDeclarations == null)
                this.typeDeclarations = new ArrayList<>();
            this.typeDeclarations.add(typeDeclarations);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.packageReference = packageReference;
        b.imports = imports;
        b.typeDeclarations = typeDeclarations;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof CompilationUnit that))
            return false;
        return Objects.equals(packageReference, that.packageReference) && Objects.equals(imports, that.imports) && Objects.equals(typeDeclarations, that.typeDeclarations);
    }

    @Override()
    public String toString() {
        return "CompilationUnit[packageReference=%s, imports=%s, typeDeclarations=%s, positionInfo=%s]".formatted(packageReference, imports, typeDeclarations, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(packageReference, imports, typeDeclarations);
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
