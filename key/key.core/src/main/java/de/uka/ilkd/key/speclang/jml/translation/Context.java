package de.uka.ilkd.key.speclang.jml.translation;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.jml.JMLInfoExtractor;
import de.uka.ilkd.key.speclang.njml.SpecMathMode;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;

/**
 * Common information that is needed almost everywhere during translation
 */
public class Context {
    /**
     * The spec math mode
     */
    public final SpecMathMode specMathMode;

    /**
     * {@code self}
     */
    public final ProgramVariable selfVar;

    /**
     * The containing class
     */
    public final KeYJavaType classType;

    public Context(@Nonnull SpecMathMode specMathMode, @Nonnull KeYJavaType classType,
            ProgramVariable selfVar) {
        this.classType = classType;
        this.specMathMode = specMathMode;
        this.selfVar = selfVar;
    }

    @Nullable
    private static ProgramVariable createSelfVar(TermBuilder tb, KeYJavaType classType,
            boolean isStaticContext) {
        return isStaticContext ? null : tb.selfVar(classType, false);
    }

    public static Context inMethod(@Nonnull IProgramMethod pm, TermBuilder tb) {
        var classType = pm.getContainerType();
        var selfVar = createSelfVar(tb, classType, pm.isStatic());
        return Context.inMethodWithSelfVar(pm, selfVar);
    }

    public static Context inMethodWithSelfVar(@Nonnull IProgramMethod pm, ProgramVariable selfVar) {
        var mode = JMLInfoExtractor.getSpecMathModeOrDefault(pm);
        return new Context(mode, pm.getContainerType(), selfVar);
    }

    public static Context inClass(@Nonnull KeYJavaType classType, boolean isStaticContext,
            TermBuilder tb) {
        var selfVar = createSelfVar(tb, classType, isStaticContext);
        var mode = JMLInfoExtractor.getSpecMathModeOrDefault(classType);
        return new Context(mode, classType, selfVar);
    }
}
