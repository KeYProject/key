/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.metaconstruct;

import java.util.LinkedHashMap;
import java.util.Map;

import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.ImmutableMap;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * Global registry of the program transformers that can occur as {@code #name(...)}
 * meta-construct statements in rule files, keyed by the meta-construct name (grammar kind), e.g.
 * {@code #unwindLoop}.
 *
 * <p>
 * The keys are read from the {@link TransformerMeta} annotation of the registered classes, which
 * is therefore the single source of truth for the names. The {@code JP2KeYConverter} uses this
 * registry to resolve the kind of a parsed meta-construct statement to its transformer.
 *
 * <p>
 * The registry intentionally covers only statement transformers: transformers that occur in
 * expression position (e.g. {@link CreateObject}, {@link ArrayLength}, {@link IsStatic} and
 * {@link TypeOf}) have dedicated grammar productions and are handled separately by the converter.
 *
 * @author Alexander Weigl
 * @version 1 (09.11.26)
 */
public final class ProgramTransformerRegistry {

    private static final ImmutableMap<String, Class<? extends ProgramTransformer>> BY_NAME =
        buildRegistry();

    private ProgramTransformerRegistry() {
    }

    /**
     * Looks up the transformer registered under the given meta-construct name.
     *
     * @param name the meta-construct name including the leading {@code #}, e.g. {@code #unwindLoop}
     * @return the corresponding {@link ProgramTransformer} class, or {@code null} if the name is
     *         not registered (unknown or reserved but not supported)
     */
    @Nullable
    public static Class<? extends ProgramTransformer> byName(@NonNull String name) {
        return BY_NAME.get(name);
    }

    /**
     * @return the number of registered transformers
     */
    public static int size() {
        return BY_NAME.size();
    }

    private static ImmutableMap<String, Class<? extends ProgramTransformer>> buildRegistry() {
        Map<String, Class<? extends ProgramTransformer>> byName = new LinkedHashMap<>();
        register(byName, SwitchToIf.class);
        register(byName, UnwindLoop.class);
        register(byName, Unpack.class);
        register(byName, ForInitUnfoldTransformer.class);
        register(byName, ForToWhile.class);
        register(byName, EnhancedForElimination.class);
        register(byName, DoBreak.class);
        register(byName, ExpandMethodBody.class);
        register(byName, MethodCall.class);
        register(byName, EvaluateArgs.class);
        register(byName, ConstructorCall.class);
        register(byName, SpecialConstructorCall.class);
        register(byName, PostWork.class);
        register(byName, StaticInitialisation.class);
        register(byName, MultipleVarDecl.class);
        register(byName, ArrayPostDecl.class);
        register(byName, InitArrayCreation.class);
        register(byName, ReattachLoopInvariant.class);
        return DefaultImmutableMap.fromMap(byName);
    }

    private static void register(
            @NonNull Map<String, Class<? extends ProgramTransformer>> byName,
            @NonNull Class<? extends ProgramTransformer> transformer) {
        final TransformerMeta meta = transformer.getAnnotation(TransformerMeta.class);
        if (meta == null) {
            throw new IllegalStateException(transformer.getSimpleName()
                + " must be annotated with @TransformerMeta to be registered");
        }
        final Class<? extends ProgramTransformer> other = byName.put(meta.name(), transformer);
        if (other != null) {
            throw new IllegalStateException("Duplicate meta-construct name " + meta.name() + " in "
                + other.getSimpleName() + " and " + transformer.getSimpleName());
        }
    }
}
