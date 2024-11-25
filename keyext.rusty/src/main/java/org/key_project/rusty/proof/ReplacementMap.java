/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof;

import java.util.LinkedHashMap;
import java.util.Map;

import org.key_project.logic.SyntaxElement;

/**
 * A map to be used in an {@link OpReplacer}. It maps operators that should be replaced to their
 * replacements.
 *
 * @author lanzinger
 *
 * @param <S> the type of the elements to replace.
 * @param <T> the type of the replacements.
 */
public interface ReplacementMap<S extends SyntaxElement, T> extends Map<S, T> {

    /**
     * Creates a new replacement map.
     *
     * @param <S> the type of the elements to replace.
     * @param <T> the type of the replacements.
     * @return a new replacement map.
     */
    static <S extends SyntaxElement, T> ReplacementMap<S, T> create() {
        return new DefaultReplacementMap<>();
    }

    /**
     * Creates a new replacement map.
     *
     * @param <S> the type of the elements to replace.
     * @param <T> the type of the replacements.
     * @param initialMappings a map whose mapping should be added to the new replacement map.
     * @return a new replacement map.
     */
    static <S extends SyntaxElement, T> ReplacementMap<S, T> create(Map<S, T> initialMappings) {
        ReplacementMap<S, T> result = create();
        result.putAll(initialMappings);
        return result;
    }

    /**
     * <p>
     * The replacement map type to use.
     * </p>
     *
     * This is just a normal {@link LinkedHashMap}.
     *
     * @author lanzinger
     *
     * @param <S> the type of the operators to replace.
     * @param <T> the type of the replacements.
     */
    class DefaultReplacementMap<S extends SyntaxElement, T> extends LinkedHashMap<S, T>
            implements ReplacementMap<S, T> {
        private static final long serialVersionUID = 6223486569442129676L;
    }
}
