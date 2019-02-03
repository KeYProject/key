package de.uka.ilkd.key.proof;

import java.util.Collection;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.settings.TermLabelSettings;
import de.uka.ilkd.key.util.LinkedHashMap;

/**
 * A map to be used in an {@link OpReplacer}.
 * It maps operators that should be replaced to their replacements.
 *
 * @author lanzinger
 *
 * @param <S> the type of the operators to replace.
 * @param <T> the type of the replacements.
 */
public interface ReplacementMap<S extends SVSubstitute, T extends SVSubstitute> extends Map<S, T> {

    /**
     * Creates a new replacement map.
     *
     * @param tf a term factory.
     * @param proof the currently loaded proof, or {@code null} if no proof is loaded.
     * @return a new replacement map.
     */
    public static <S extends SVSubstitute, T extends SVSubstitute>
    ReplacementMap<S, T> create(TermFactory tf, Proof proof) {
        if (proof != null && proof.getSettings().getTermLabelSettings().getUseOriginLabels()) {
            return new NoIrrelevantLabelsReplacementMap<S, T>(tf);
        } else {
            return new DefaultReplacementMap<S, T>();
        }
    }

    /**
     * Creates a new replacement map.
     *
     * @param tf a term factory.
     * @param proof the currently loaded proof, or {@code null} if no proof is loaded.
     * @param initialMappings a map whose mapping should be added to the new replacement map.
     * @return a new replacement map.
     */
    public static <S extends SVSubstitute, T extends SVSubstitute>
    ReplacementMap<S, T> create(TermFactory tf, Proof proof, Map<S, T> initialMappings) {
        ReplacementMap<S, T> result = create(tf, proof);
        result.putAll(initialMappings);
        return result;
    }

    /**
     * <p>
     * The replacement map type to use if {@link TermLabelSettings#getUseOriginLabels()} is false. </p>
     *
     * This is just a normal {@link LinkedHashMap}.
     *
     * @author lanzinger
     *
     * @param <S> the type of the operators to replace.
     * @param <T> the type of the replacements.
     */
    public static class DefaultReplacementMap<S extends SVSubstitute, T extends SVSubstitute>
    extends LinkedHashMap<S, T>
    implements ReplacementMap<S, T> { }

    /**
     * <p>
     * The replacement map type to use if {@link TermLabelSettings#getUseOriginLabels()} is true. </p>
     *
     * <p> This map considers otherwise equal terms with different origins as equal. </p>
     *
     * @author lanzinger
     *
     * @param <S> the type of the operators to replace.
     * @param <T> the type of the replacements.
     *
     * @see OriginTermLabel
     */
    public static class NoIrrelevantLabelsReplacementMap
    <S extends SVSubstitute, T extends SVSubstitute> implements ReplacementMap<S, T> {

        /**
         * The map wrapped by this one.
         */
        private Map<S, T> map = new LinkedHashMap<>();

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
                Term old = (Term) obj;

                Term result = tf.createTerm(
                        old.op(),
                        new ImmutableArray<>(
                                old.subs().stream().map(this::wrap).collect(Collectors.toList())),
                        old.boundVars(),
                        old.javaBlock(),
                        new ImmutableArray<>(
                                old.getLabels().stream()
                                .filter(TermLabel::isStrategyRelevant).collect(Collectors.toList())));

                return (R) result;
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
            m.forEach((k, v) -> put(k, v));
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
