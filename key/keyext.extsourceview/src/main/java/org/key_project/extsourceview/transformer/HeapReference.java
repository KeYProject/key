package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.origin.OriginRef;
import de.uka.ilkd.key.logic.origin.OriginRefType;
import org.key_project.util.collection.ImmutableList;

import javax.annotation.Nullable;
import java.util.Collection;
import java.util.Optional;

/**
 * This class represents a single reference to a heap
 * Such a reference is build from a list of heap-update terms
 */
public class HeapReference {
    public enum HeapUpdateType {
        STORE("STORE"),
        ANON("ANON"),
        HEAP("HEAP");

        public final String key;

        HeapUpdateType(String k) {
            key= k;
        }

        @Override
        public String toString() {
            return key;
        }
    }

    public static class HeapUpdate {
        public final HeapUpdateType Type;
        public final Term Term1;
        public final Term Term2;
        public final Term Term3;
        public final @Nullable OriginRef Origin;

        public HeapUpdate(HeapUpdateType type, Term term1, Term term2, Term term3, @Nullable OriginRef origin) {
            Type = type;
            Term1 = term1;
            Term2 = term2;
            Term3 = term3;
            Origin = origin;
        }
    }

    public final ImmutableList<HeapUpdate> updates;

    public HeapReference(ImmutableList<HeapUpdate> updates) {
        this.updates = updates;
    }

    public HeapReference(Collection<HeapUpdate> updates) {
        this.updates = ImmutableList.fromList(updates);
    }

    public Optional<Integer> getLineNumber() {
        return this.updates.stream().
                filter(p -> p.Origin != null).
                filter(p -> p.Origin.hasFile()).
                map(p -> p.Origin.LineEnd).
                max(Integer::compareTo);
    }

    public static HeapReference.HeapUpdate newStoreUpdate(Term t) {
        var origin = t.getOriginRef().
            stream().
            filter(p -> p.Type == OriginRefType.JAVA_STMT || p.Type == OriginRefType.LOOP_ANONUPDATE || p.Type == OriginRefType.OPERATION_ANONUPDATE).
            findFirst().
            orElse(null);
        return new HeapUpdate(HeapUpdateType.STORE, t.sub(1), t.sub(2), t.sub(3), origin);
    }

    public static HeapReference.HeapUpdate newAnonUpdate(Term t) {
        var origin = t.getOriginRef().
                stream().
                filter(p -> p.Type == OriginRefType.JAVA_STMT || p.Type == OriginRefType.LOOP_ANONUPDATE || p.Type == OriginRefType.OPERATION_ANONUPDATE).
                filter(p -> p.hasFile()).
                findFirst().
                orElse(null);
        return new HeapUpdate(HeapUpdateType.ANON, t.sub(1), t.sub(2), null, origin);
    }

    public static HeapUpdate newHeap(Term t) {
        var origin = t.getOriginRef().
                stream().
                filter(p -> p.Type == OriginRefType.JAVA_STMT || p.Type == OriginRefType.LOOP_ANONUPDATE || p.Type == OriginRefType.OPERATION_ANONUPDATE).
                findFirst().
                orElse(null);
        return new HeapUpdate(HeapUpdateType.HEAP, t, null, null, origin);
    }

    public boolean heapEquals(HeapReference other) {
        var ln1 = this.getLineNumber();
        var ln2 = other.getLineNumber();

        if (ln1.isPresent() && ln2.isPresent()) {
            return ln1.get().equals(ln2.get());
        }

        if (ln1.isEmpty() && ln2.isEmpty()) {
            return true;
        }

        return false;
    }
}
