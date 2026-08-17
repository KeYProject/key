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
public final class EnhancedFor extends JavaSourceElement implements LoopStatement {

    private final ImmutableList<TextualJMLConstruct> attachedJml;

    private final Statement body;

    private final IGuard guard;

    private final ILoopInit inits;

    @EqEx
    @Nullable
    private final PositionInfo positionInfo;

    private final IForUpdates updates;

    @java.lang.Override()
    public ImmutableList<TextualJMLConstruct> attachedJml() {
        return attachedJml;
    }

    @java.lang.Override()
    public Statement body() {
        return body;
    }

    @java.lang.Override()
    public IGuard guard() {
        return guard;
    }

    @java.lang.Override()
    public ILoopInit inits() {
        return inits;
    }

    @Nullable()
    @java.lang.Override()
    public PositionInfo positionInfo() {
        return positionInfo;
    }

    @java.lang.Override()
    public IForUpdates updates() {
        return updates;
    }

    public EnhancedFor(ImmutableList<TextualJMLConstruct> attachedJml, Statement body, IGuard guard, ILoopInit inits, @EqEx @Nullable PositionInfo positionInfo, IForUpdates updates) {
        this.attachedJml = Objects.requireNonNull(attachedJml);
        this.body = Objects.requireNonNull(body);
        this.guard = Objects.requireNonNull(guard);
        this.inits = Objects.requireNonNull(inits);
        this.positionInfo = positionInfo;
        this.updates = Objects.requireNonNull(updates);
    }

    public EnhancedFor(ImmutableList<TextualJMLConstruct> attachedJml, Statement body, IGuard guard, ILoopInit inits, IForUpdates updates) {
        this.attachedJml = Objects.requireNonNull(attachedJml);
        this.body = Objects.requireNonNull(body);
        this.guard = Objects.requireNonNull(guard);
        this.inits = Objects.requireNonNull(inits);
        this.positionInfo = null;
        this.updates = Objects.requireNonNull(updates);
    }

    public EnhancedFor(EnhancedFor other) {
        this(other.attachedJml, other.body, other.guard, other.inits, other.positionInfo, other.updates);
    }

    @Override()
    @Nullable()
    public MatchConditions match(java.lang.Object o, MatchConditions cond) {
        if (!(o instanceof EnhancedFor other))
            return null;
        cond = MatchHelper.match(attachedJml, other.attachedJml, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(body, other.body, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(guard, other.guard, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(inits, other.inits, cond);
        if (cond == null) {
            return null;
        }
        cond = MatchHelper.match(updates, other.updates, cond);
        if (cond == null) {
            return null;
        }
        return cond;
    }

    public EnhancedFor withAttachedJml(ImmutableList<TextualJMLConstruct> attachedJml) {
        return new EnhancedFor(attachedJml, body(), guard(), inits(), positionInfo(), updates());
    }

    public EnhancedFor withBody(Statement body) {
        return new EnhancedFor(attachedJml(), body, guard(), inits(), positionInfo(), updates());
    }

    public EnhancedFor withGuard(IGuard guard) {
        return new EnhancedFor(attachedJml(), body(), guard, inits(), positionInfo(), updates());
    }

    public EnhancedFor withInits(ILoopInit inits) {
        return new EnhancedFor(attachedJml(), body(), guard(), inits, positionInfo(), updates());
    }

    public EnhancedFor withPositionInfo(PositionInfo positionInfo) {
        return new EnhancedFor(attachedJml(), body(), guard(), inits(), positionInfo, updates());
    }

    public EnhancedFor withUpdates(IForUpdates updates) {
        return new EnhancedFor(attachedJml(), body(), guard(), inits(), positionInfo(), updates);
    }

    public final static class Builder {

        @Nullable()
        public ImmutableList<TextualJMLConstruct> attachedJml;

        @Nullable()
        public Statement body;

        @Nullable()
        public IGuard guard;

        @Nullable()
        public ILoopInit inits;

        @Nullable()
        public PositionInfo positionInfo;

        @Nullable()
        public IForUpdates updates;

        public EnhancedFor build() {
            return new EnhancedFor(attachedJml, body, guard, inits, positionInfo, updates);
        }

        public Builder attachedJml(ImmutableList<TextualJMLConstruct> attachedJml) {
            this.attachedJml = attachedJml;
            return this;
        }

        public Builder body(Statement body) {
            this.body = body;
            return this;
        }

        public Builder guard(IGuard guard) {
            this.guard = guard;
            return this;
        }

        public Builder inits(ILoopInit inits) {
            this.inits = inits;
            return this;
        }

        public Builder positionInfo(PositionInfo positionInfo) {
            this.positionInfo = positionInfo;
            return this;
        }

        public Builder updates(IForUpdates updates) {
            this.updates = updates;
            return this;
        }

        public Builder attachedJml(TextualJMLConstruct attachedJml) {
            if (this.attachedJml == null)
                this.attachedJml = new ArrayList<>();
            this.attachedJml.add(attachedJml);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.attachedJml = attachedJml;
        b.body = body;
        b.guard = guard;
        b.inits = inits;
        b.positionInfo = positionInfo;
        b.updates = updates;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof EnhancedFor that))
            return false;
        return Objects.equals(attachedJml, that.attachedJml) && Objects.equals(body, that.body) && Objects.equals(guard, that.guard) && Objects.equals(inits, that.inits) && Objects.equals(updates, that.updates);
    }

    @Override()
    public String toString() {
        return "EnhancedFor[attachedJml=%s, body=%s, guard=%s, inits=%s, positionInfo=%s, updates=%s]".formatted(attachedJml, body, guard, inits, positionInfo, updates);
    }

    @EqEx()
    @Nullable()
    @Internal()
    private Integer hashCode;

    @Override()
    public int hashCode() {
        if (hashCode == null)
            hashCode = Objects.hash(attachedJml, body, guard, inits, updates);
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
