/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.TermLabelSettings;
import de.uka.ilkd.key.util.LinkedHashMap;

/**
 * A map to be used in an {@link OpReplacer}. It maps operators that should be replaced to their
 * replacements.
 *
 * @author lanzinger
 *
 * @param <S> the type of the elements to replace.
 * @param <T> the type of the replacements.
 */
public interface ReplacementMap<S extends SVSubstitute, T> extends Map<S, T> {

    /**
     * Creates a new replacement map.
     *
     * @param <S> the type of the elements to replace.
     * @param <T> the type of the replacements.
     * @param tf a term factory.
     * @param proof the currently loaded proof, or {@code null} if no proof is loaded.
     * @return a new replacement map.
     */
    static <S extends SVSubstitute, T> ReplacementMap<S, T> create(TermFactory tf,
            Proof proof) {
        if (ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings().getUseOriginLabels()) {
            return new NoIrrelevantLabelsReplacementMap<>(tf);
        } else {
            return new DefaultReplacementMap<>();
        }
    }

    /**
     * Creates a new replacement map.
     *
     * @param <S> the type of the elements to replace.
     * @param <T> the type of the replacements.
     * @param tf a term factory.
     * @param proof the currently loaded proof, or {@code null} if no proof is loaded.
     * @param initialMappings a map whose mapping should be added to the new replacement map.
     * @return a new replacement map.
     */
    static <S extends SVSubstitute, T> ReplacementMap<S, T> create(TermFactory tf,
            Proof proof, Map<S, T> initialMappings) {
        ReplacementMap<S, T> result = create(tf, proof);
        result.putAll(initialMappings);
        return result;
    }

    /**
     * <p>
     * The replacement map type to use if {@link TermLabelSettings#getUseOriginLabels()} is false.
     * </p>
     *
     * This is just a normal {@link LinkedHashMap}.
     *
     * @author lanzinger
     *
     * @param <S> the type of the operators to replace.
     * @param <T> the type of the replacements.
     */
    class DefaultReplacementMap<S extends SVSubstitute, T> extends LinkedHashMap<S, T>
            implements ReplacementMap<S, T> {
        private static final long serialVersionUID = 6223486569442129676L;
    }

    /**
     * <p>
     * The replacement map type to use if {@link TermLabelSettings#getUseOriginLabels()} is true.
     * </p>
     *
     * <p>
     * This map considers otherwise equal terms with different origins as equal.
     * </p>
     *
     * @author lanzinger
     *
     * @param <S> the type of the operators to replace.
     * @param <T> the type of the replacements.
     *
     * @see OriginTermLabel
     */
    class NoIrrelevantLabelsReplacementMap<S extends SVSubstitute, T>
            implements ReplacementMap<S, T> {

        /**
         * The map wrapped by this one.
         */
        private final Map<S, T> map = new LinkedHashMap<>();

        /**
         * Term factory.
         */
        private final TermFactory tf;

        /**
         * Create a new map
         *
         * @param tf a term factory.
         */
        public NoIrrelevantLabelsReplacementMap(TermFactory tf) {
            this.tf = tf;
        }

        @SuppressWarnings("unchecked")
        private <R> R wrap(R obj) {
            if (obj instanceof Term) {
                return (R) TermLabel.removeIrrelevantLabels((Term) obj, tf);
            } else {
                return obj;
            }
        }

        @Override
        public int size() {
            return map.size();
        }

        @Override
        public boolean isEmpty() {
            return map.isEmpty();
        }

        @Override
        public boolean containsKey(Object key) {
            return map.containsKey(wrap(key));
        }

        @Override
        public boolean containsValue(Object value) {
            return map.containsValue(value);
        }

        @Override
        public T get(Object key) {
            return map.get(wrap(key));
        }

        @Override
        public T put(S key, T value) {
            return map.put(wrap(key), value);
        }

        @Override
        public T remove(Object key) {
            return map.remove(wrap(key));
        }

        @Override
        public void putAll(Map<? extends S, ? extends T> m) {
            m.forEach(this::put);
        }

        @Override
        public void clear() {
            map.clear();
        }

        @Override
        public Set<S> keySet() {
            return map.keySet();
        }

        @Override
        public Collection<T> values() {
            return map.values();
        }

        @Override
        public Set<Entry<S, T>> entrySet() {
            return map.entrySet();
        }
    }

}
