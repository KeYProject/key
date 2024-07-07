package de.uka.ilkd.key.speclang.jml.translation;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;

/**
 * Common information that is needed almost everywhere during translation. Class is immutable.
 *
 * @author Julian Wiesler
 */
public class Context {

    /**
     * {@code self}
     */
    public final ProgramVariable selfVar;

    /**
     * The containing class
     */
    public final KeYJavaType classType;

    /**
     * Constructs a new context from the given parameters
     *
     * @param classType class
     * @param selfVar self variable
     */
    public Context(@Nonnull KeYJavaType classType,
                   ProgramVariable selfVar) {
        this.classType = classType;
        this.selfVar = selfVar;
    }

    /**
     * Constructs a self var from the given parameters
     *
     * @param tb term builder
     * @param classType class
     * @param isStaticContext whether this is a static context
     */
    @Nullable
    private static ProgramVariable createSelfVar(TermBuilder tb, KeYJavaType classType,
            boolean isStaticContext) {
        return isStaticContext ? null : tb.selfVar(classType, false);
    }

    /**
     * Constructs a new context in the given program method
     *
     * @param pm program method
     * @param tb term builder
     */
    public static Context inMethod(@Nonnull IProgramMethod pm, TermBuilder tb) {
        var classType = pm.getContainerType();
        var selfVar = createSelfVar(tb, classType, pm.isStatic());
        return Context.inMethodWithSelfVar(pm, selfVar);
    }

    /**
     * Constructs a new context in the given program method using the given self var
     *
     * @param pm program method
     * @param selfVar self var
     */
    public static Context inMethodWithSelfVar(@Nonnull IProgramMethod pm, ProgramVariable selfVar) {
        return new Context(pm.getContainerType(), selfVar);
    }

    /**
     * Constructs a new context in the given class
     *
     * @param classType class
     * @param isStaticContext whether this is a static context
     * @param tb term builder
     */
    public static Context inClass(@Nonnull KeYJavaType classType, boolean isStaticContext,
            TermBuilder tb) {
        var selfVar = createSelfVar(tb, classType, isStaticContext);
        return new Context(classType, selfVar);
    }
}
