package de.uka.ilkd.key.proof;

import java.util.Collection;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.sort.Sort;
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
     * @param services services.
     * @return a new replacement map.
     */
    public static <S extends SVSubstitute, T extends SVSubstitute>
    ReplacementMap<S, T> create(Services services) {
        Proof proof = services.getProof();

        if (proof != null && proof.getSettings().getTermLabelSettings().getUseOriginLabels()) {
            return new NoIrrelevantLabelsReplacementMap<S, T>();
        } else {
            return new DefaultReplacementMap<S, T>();
        }
    }
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
class DefaultReplacementMap<S extends SVSubstitute, T extends SVSubstitute>
    extends LinkedHashMap<S, T>
    implements ReplacementMap<S, T> { }

/**
 * <p>
 * The replacement map type to use if {@link TermLabelSettings#getUseOriginLabels()} is true. </p>
 *
 * <p> This map uses other {@code hashCode} and {@code equals} methods so that otherwise equal
 * terms with different origins are considered equal. </p>
 *
 * @author lanzinger
 *
 * @param <S> the type of the operators to replace.
 * @param <T> the type of the replacements.
 */
class NoIrrelevantLabelsReplacementMap<S extends SVSubstitute, T extends SVSubstitute> implements ReplacementMap<S, T> {

    private Map<S, T> map = new LinkedHashMap<>();

    @SuppressWarnings("unchecked")
    private static <T> T wrap(T obj) {
        if (obj instanceof Term && !(obj instanceof TermWrapper)) {
            return (T) new TermWrapper((Term) obj);
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
        return map.keySet().stream().map(
                NoIrrelevantLabelsReplacementMap::wrap).collect(Collectors.toSet());
    }

    @Override
    public Collection<T> values() {
        return map.values();
    }

    @Override
    public Set<Entry<S, T>> entrySet() {
        return map.entrySet().stream().collect(
                Collectors.toMap(e -> wrap(e.getKey()), Entry::getValue)).entrySet();
    }
}

/**
 * <p> Wrapper used in {@link NoIrrelevantLabelsReplacementMap}. </p>
 *
 * <p> This wrapper behaves the same as the term it wraps, except that irrelevant term labels are
 * not considered for {@link Object#equals(Object)} and {@link Object#hashCode()}. </p>
 *
 * @author lanzinger
 */
class TermWrapper implements Term {

    private int hash;
    private Term term;

    TermWrapper(Term term) {
        this.term = term;
    }

    private int computeHashCode() {
        int hash = 5;
        hash = hash * 17 + op().hashCode();
        hash = hash * 17 + subs().hashCode();
        hash = hash * 17 + boundVars().hashCode();
        hash = hash * 17 + javaBlock().hashCode();

        hash += getLabels().stream().filter(TermLabel::isStrategyRelevant).reduce(
                0,
                (acc, el) -> acc + 7 * el.hashCode(),
                Integer::sum);

        return hash;
    }

    @Override
    public final int hashCode() {
        if(hash == -1) {
            hash = computeHashCode();
        }

        return hash;
    }

    @Override
    public boolean equalsModIrrelevantTermLabels(Object o) {
        return term.equalsModIrrelevantTermLabels(o);
    }

    @Override
    public boolean equals(Object obj) {
        return term.equalsModIrrelevantTermLabels(obj);
    }

    @Override
    public Operator op() {
        return term.op();
    }

    @Override
    public <T> T op(Class<T> opClass) throws IllegalArgumentException {
        return term.op(opClass);
    }

    @Override
    public ImmutableArray<Term> subs() {
        return term.subs();
    }

    @Override
    public Term sub(int n) {
        return term.sub(n);
    }

    @Override
    public ImmutableArray<QuantifiableVariable> boundVars() {
        return term.boundVars();
    }

    @Override
    public ImmutableArray<QuantifiableVariable> varsBoundHere(int n) {
        return term.varsBoundHere(n);
    }

    @Override
    public JavaBlock javaBlock() {
        return term.javaBlock();
    }

    @Override
    public int arity() {
        return term.arity();
    }

    @Override
    public Sort sort() {
        return term.sort();
    }

    @Override
    public int depth() {
        return term.depth();
    }

    @Override
    public boolean isRigid() {
        return term.isRigid();
    }

    @Override
    public ImmutableSet<QuantifiableVariable> freeVars() {
        return term.freeVars();
    }

    @Override
    public void execPostOrder(Visitor visitor) {
        term.execPostOrder(visitor);
    }

    @Override
    public void execPreOrder(Visitor visitor) {
        term.execPreOrder(visitor);
    }

    @Override
    public boolean equalsModRenaming(Term o) {
        return term.equalsModRenaming(o);
    }

    @Override
    public boolean hasLabels() {
        return term.hasLabels();
    }

    @Override
    public boolean containsLabel(TermLabel label) {
        return term.containsLabel(label);
    }

    @Override
    public ImmutableArray<TermLabel> getLabels() {
        return term.getLabels();
    }

    @Override
    public TermLabel getLabel(Name termLabelName) {
        return term.getLabel(termLabelName);
    }

    @Override
    public int serialNumber() {
        return term.serialNumber();
    }

    @Override
    public boolean containsJavaBlockRecursive() {
        return term.containsJavaBlockRecursive();
    }
}
