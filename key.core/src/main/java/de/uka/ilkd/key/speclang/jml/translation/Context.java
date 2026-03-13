/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.translation;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.speclang.jml.JMLInfoExtractor;
import de.uka.ilkd.key.speclang.njml.SpecMathMode;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * Common information that is needed almost everywhere during translation. Class is immutable.
 *
 * @param specMathMode The spec math mode
 * @param selfVar {@code self}
 * @param classType The containing class
 * @author Julian Wiesler
 */
public record Context(@NonNull SpecMathMode specMathMode, @NonNull KeYJavaType classType,
        LocationVariable selfVar) {
    /**
     * Constructs a self var from the given parameters
     *
     * @param tb term builder
     * @param classType class
     * @param isStaticContext whether this is a static context
     */
    private static @Nullable LocationVariable createSelfVar(TermBuilder tb, KeYJavaType classType,
            boolean isStaticContext) {
        return isStaticContext ? null : tb.selfVar(classType, false);
    }

    /**
     * Constructs a new context in the given program method
     *
     * @param pm program method
     * @param tb term builder
     */
    public static Context inMethod(@NonNull IProgramMethod pm, TermBuilder tb) {
        var classType = pm.getContainerType();
        var selfVar = createSelfVar(tb, classType, pm.isStatic());
        return inMethodWithSelfVar(pm, selfVar);
    }

    /**
     * Constructs a new context in the given program method using the given self var
     *
     * @param pm program method
     * @param selfVar self var
     */
    public static Context inMethodWithSelfVar(@NonNull IProgramMethod pm,
            LocationVariable selfVar) {
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
    public static Context inClass(@NonNull KeYJavaType classType, boolean isStaticContext,
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
