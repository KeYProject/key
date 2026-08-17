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
public final class NewArray extends JavaSourceElement implements TypeOperator {

    private final int dimensions;

    private final ArrayInitializer arrayInitializer;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    private final TypeReference typeReference;

    public int dimensions() {
        return dimensions;
    }

    public ArrayInitializer arrayInitializer() {
        return arrayInitializer;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    @java.lang.Override()
    public TypeReference typeReference() {
        return typeReference;
    }

    public NewArray(int dimensions, ArrayInitializer arrayInitializer, @EqEx @Nullable PositionInfo positionInfo, TypeReference typeReference) {
        this.dimensions = Objects.requireNonNull(dimensions);
        this.arrayInitializer = Objects.requireNonNull(arrayInitializer);
        this.positionInfo = positionInfo;
        this.typeReference = Objects.requireNonNull(typeReference);
    }

    public NewArray(int dimensions, ArrayInitializer arrayInitializer, TypeReference typeReference) {
        this.dimensions = Objects.requireNonNull(dimensions);
        this.arrayInitializer = Objects.requireNonNull(arrayInitializer);
        this.positionInfo = null;
        this.typeReference = Objects.requireNonNull(typeReference);
    }

    public NewArray(NewArray other) {
        this(other.dimensions, other.arrayInitializer, other.positionInfo, other.typeReference);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof NewArray other))
            return null;
        cond = MatchHelper.match(dimensions, other.dimensions, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(arrayInitializer, other.arrayInitializer, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(typeReference, other.typeReference, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public NewArray withDimensions(int dimensions) {
        return new NewArray(dimensions, arrayInitializer(), positionInfo(), typeReference());
    }

    public NewArray withArrayInitializer(ArrayInitializer arrayInitializer) {
        return new NewArray(dimensions(), arrayInitializer, positionInfo(), typeReference());
    }

    public NewArray withPositionInfo(PositionInfo positionInfo) {
        return new NewArray(dimensions(), arrayInitializer(), positionInfo, typeReference());
    }

    public NewArray withTypeReference(TypeReference typeReference) {
        return new NewArray(dimensions(), arrayInitializer(), positionInfo(), typeReference);
    }

    public final static class Builder {

        @Nullable()
        public int dimensions;

        @Nullable()
        public ArrayInitializer arrayInitializer;

        @Nullable()
        public PositionInfo positionInfo;

        @Nullable()
        public TypeReference typeReference;

        public NewArray build() {
            return new NewArray(dimensions, arrayInitializer, positionInfo, typeReference);
        }

        public Builder dimensions(int dimensions) {
            this.dimensions = dimensions;
            return this;
        }

        public Builder arrayInitializer(ArrayInitializer arrayInitializer) {
            this.arrayInitializer = arrayInitializer;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }

        public Builder typeReference(TypeReference typeReference) {
            this.typeReference = typeReference;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.dimensions = dimensions;
        b.arrayInitializer = arrayInitializer;
        b.positionInfo = positionInfo;
        b.typeReference = typeReference;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof NewArray that))
            return false;
        return Objects.equals(dimensions, that.dimensions) && Objects.equals(arrayInitializer, that.arrayInitializer) && Objects.equals(typeReference, that.typeReference);
    }

    @Override()
    public String toString() {
        return "NewArray[dimensions=%s, arrayInitializer=%s, positionInfo=%s, typeReference=%s]".formatted(dimensions, arrayInitializer, positionInfo, typeReference);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(dimensions, arrayInitializer, typeReference);
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
