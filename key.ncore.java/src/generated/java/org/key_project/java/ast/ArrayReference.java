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
public final class ArrayReference extends JavaSourceElement implements JavaProgramElement {

    private final ReferencePrefix prefix;

    private final ImmutableList<Expression> inits;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    public ReferencePrefix prefix() {
        return prefix;
    }

    public ImmutableList<Expression> inits() {
        return inits;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    public ArrayReference(ReferencePrefix prefix, ImmutableList<Expression> inits, @EqEx @Nullable PositionInfo positionInfo) {
        this.prefix = Objects.requireNonNull(prefix);
        this.inits = Objects.requireNonNull(inits);
        this.positionInfo = positionInfo;
    }

    public ArrayReference(ReferencePrefix prefix, ImmutableList<Expression> inits) {
        this.prefix = Objects.requireNonNull(prefix);
        this.inits = Objects.requireNonNull(inits);
        this.positionInfo = null;
    }

    public ArrayReference(ArrayReference other) {
        this(other.prefix, other.inits, other.positionInfo);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof ArrayReference other))
            return null;
        cond = MatchHelper.match(prefix, other.prefix, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(inits, other.inits, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public ArrayReference withPrefix(ReferencePrefix prefix) {
        return new ArrayReference(prefix, inits(), positionInfo());
    }

    public ArrayReference withInits(ImmutableList<Expression> inits) {
        return new ArrayReference(prefix(), inits, positionInfo());
    }

    public ArrayReference withPositionInfo(PositionInfo positionInfo) {
        return new ArrayReference(prefix(), inits(), positionInfo);
    }

    public final static class Builder {

        @Nullable()
        public ReferencePrefix prefix;

        @Nullable()
        public ImmutableList<Expression> inits;

        @Nullable()
        public PositionInfo positionInfo;

        public ArrayReference build() {
            return new ArrayReference(prefix, inits, positionInfo);
        }

        public Builder prefix(ReferencePrefix prefix) {
            this.prefix = prefix;
            return this;
        }

        public Builder inits(ImmutableList<Expression> inits) {
            this.inits = inits;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }

        public Builder inits(Expression inits) {
            if (this.inits == null)
                this.inits = new ArrayList<>();
            this.inits.add(inits);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.prefix = prefix;
        b.inits = inits;
        b.positionInfo = positionInfo;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof ArrayReference that))
            return false;
        return Objects.equals(prefix, that.prefix) && Objects.equals(inits, that.inits);
    }

    @Override()
    public String toString() {
        return "ArrayReference[prefix=%s, inits=%s, positionInfo=%s]".formatted(prefix, inits, positionInfo);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(prefix, inits);
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
