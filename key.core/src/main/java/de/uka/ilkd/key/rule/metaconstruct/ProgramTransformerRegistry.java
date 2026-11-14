/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.metaconstruct;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.ImmutableMap;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * Global registry of the transformers that can occur as {@code #name(...)} meta-constructs in
 * rule files, keyed by the meta-construct name (grammar kind), e.g. {@code #unwindLoop}.
 *
 * <p>
 * The {@link TransformerMeta} annotation of the registered classes is the single source of truth
 * for the names and is checked to be present and unique. Two separate maps keep the two usages
 * apart:
 * <ul>
 * <li>{@link #byName(String)}: statement-position transformers, which are parsed as
 * {@code KeyMetaConstruct} statements.</li>
 * <li>{@link #expressionByName(String)}: expression-position transformers, which either have a
 * dedicated grammar production ({@link TypeOf}) or no grammar token at all and therefore parse as
 * ordinary method calls ({@link CreateObject}, {@link ArrayLength}).</li>
 * </ul>
 *
 * <p>
 * The {@code JP2KeYConverter} uses both lookups to resolve a meta-construct name to its
 * transformer and instantiates the transformer by matching one of its constructors against the
 * converted arguments, and the {@code JavaParserFactory} configures the JMLtk parser (via
 * {@code ParserConfiguration#setKeyMetaConstructNames}) with {@link #names()} so that only the
 * statement names are recognized as meta-construct statements.
 *
 * @author Alexander Weigl
 * @version 1 (09.11.26)
 */
public final class ProgramTransformerRegistry {

    private static final ImmutableMap<String, Class<? extends ProgramTransformer>> BY_NAME;
    private static final ImmutableMap<String, Class<? extends ProgramTransformer>> EXPRESSION_BY_NAME;
    private static final Set<String> NAMES;

    static {
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
        BY_NAME = DefaultImmutableMap.fromMap(byName);
        NAMES = Collections.unmodifiableSet(new LinkedHashSet<>(byName.keySet()));

        Map<String, Class<? extends ProgramTransformer>> expressionByName = new LinkedHashMap<>();
        register(expressionByName, CreateObject.class);
        register(expressionByName, ArrayLength.class);
        register(expressionByName, TypeOf.class);
        register(expressionByName, IsStatic.class);
        EXPRESSION_BY_NAME = DefaultImmutableMap.fromMap(expressionByName);
    }

    private ProgramTransformerRegistry() {
    }

    /**
     * Looks up the statement transformer registered under the given meta-construct name.
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
     * Looks up the expression transformer registered under the given name.
     *
     * @param name the meta-construct name including the leading {@code #}, e.g.
     *        {@code #createObject}
     * @return the corresponding {@link ProgramTransformer} class, or {@code null} if the name is
     *         not registered
     */
    @Nullable
    public static Class<? extends ProgramTransformer> expressionByName(@NonNull String name) {
        return EXPRESSION_BY_NAME.get(name);
    }

    /**
     * @return the statement names (grammar kinds) of all registered transformers as an unmodifiable
     *         set
     */
    public static Set<String> names() {
        return NAMES;
    }

    /**
     * @return the number of registered statement transformers
     */
    public static int size() {
        return BY_NAME.size();
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
