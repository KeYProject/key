/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.translation;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.jml.JMLInfoExtractor;
import de.uka.ilkd.key.speclang.njml.SpecMathMode;

/**
 * Common information that is needed almost everywhere during translation. Class is immutable.
 *
 * @author Julian Wiesler
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

    /**
     * Constructs a new context from the given parameters
     *
     * @param specMathMode spec math mode
     * @param classType class
     * @param selfVar self variable
     */
    public Context(@Nonnull SpecMathMode specMathMode, @Nonnull KeYJavaType classType,
            ProgramVariable selfVar) {
        this.classType = classType;
        this.specMathMode = specMathMode;
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
        var mode = JMLInfoExtractor.getSpecMathModeOrDefault(pm);
        return new Context(mode, pm.getContainerType(), selfVar);
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
        var mode = JMLInfoExtractor.getSpecMathModeOrDefault(classType);
        return new Context(mode, classType, selfVar);
    }

    /**
     * Constructs a new context while entering the given spec math mode
     *
     * @param mode spec math mode
     */
    public Context orWithSpecMathMode(@Nullable SpecMathMode mode) {
        return mode == null ? this : new Context(mode, this.classType, this.selfVar);
    }
}
